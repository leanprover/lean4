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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
size_t v_x_1072__boxed_285_; size_t v_x_1073__boxed_286_; lean_object* v_res_287_; 
v_x_1072__boxed_285_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_x_1073__boxed_286_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_res_287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_280_, v_x_1072__boxed_285_, v_x_1073__boxed_286_, v_x_283_, v_x_284_);
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
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_nbuckets_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_342_ = lean_array_get_size(v_data_341_);
v___x_343_ = lean_unsigned_to_nat(2u);
v_nbuckets_344_ = lean_nat_mul(v___x_342_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_box(0);
v___x_347_ = lean_mk_array(v_nbuckets_344_, v___x_346_);
v___x_348_ = lean_array_propagate_mark(v_data_341_, v___x_347_);
v___x_349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_345_, v_data_341_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
uint8_t v___x_352_; 
v___x_352_ = 0;
return v___x_352_;
}
else
{
lean_object* v_key_353_; lean_object* v_tail_354_; uint8_t v___x_355_; 
v_key_353_ = lean_ctor_get(v_x_351_, 0);
v_tail_354_ = lean_ctor_get(v_x_351_, 2);
v___x_355_ = lean_name_eq(v_key_353_, v_a_350_);
if (v___x_355_ == 0)
{
v_x_351_ = v_tail_354_;
goto _start;
}
else
{
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_357_, v_x_358_);
lean_dec(v_x_358_);
lean_dec(v_a_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_361_, lean_object* v_b_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_dec(v_b_362_);
lean_dec(v_a_361_);
return v_x_363_;
}
else
{
lean_object* v_key_364_; lean_object* v_value_365_; lean_object* v_tail_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_378_; 
v_key_364_ = lean_ctor_get(v_x_363_, 0);
v_value_365_ = lean_ctor_get(v_x_363_, 1);
v_tail_366_ = lean_ctor_get(v_x_363_, 2);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_363_);
if (v_isSharedCheck_378_ == 0)
{
v___x_368_ = v_x_363_;
v_isShared_369_ = v_isSharedCheck_378_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_tail_366_);
lean_inc(v_value_365_);
lean_inc(v_key_364_);
lean_dec(v_x_363_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_378_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; 
v___x_370_ = lean_name_eq(v_key_364_, v_a_361_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_361_, v_b_362_, v_tail_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 2, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_key_364_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_value_365_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
else
{
lean_object* v___x_376_; 
lean_dec(v_value_365_);
lean_dec(v_key_364_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_b_362_);
lean_ctor_set(v___x_368_, 0, v_a_361_);
v___x_376_ = v___x_368_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_b_362_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_tail_366_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_379_, lean_object* v_a_380_, lean_object* v_b_381_){
_start:
{
lean_object* v_size_382_; lean_object* v_buckets_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_429_; 
v_size_382_ = lean_ctor_get(v_m_379_, 0);
v_buckets_383_ = lean_ctor_get(v_m_379_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_m_379_);
if (v_isSharedCheck_429_ == 0)
{
v___x_385_ = v_m_379_;
v_isShared_386_ = v_isSharedCheck_429_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_buckets_383_);
lean_inc(v_size_382_);
lean_dec(v_m_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_429_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; uint64_t v___y_389_; 
v___x_387_ = lean_array_get_size(v_buckets_383_);
if (lean_obj_tag(v_a_380_) == 0)
{
uint64_t v___x_427_; 
v___x_427_ = 1723ULL;
v___y_389_ = v___x_427_;
goto v___jp_388_;
}
else
{
uint64_t v_hash_428_; 
v_hash_428_ = lean_ctor_get_uint64(v_a_380_, sizeof(void*)*2);
v___y_389_ = v_hash_428_;
goto v___jp_388_;
}
v___jp_388_:
{
uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v_fold_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v_bkt_401_; uint8_t v___x_402_; 
v___x_390_ = 32ULL;
v___x_391_ = lean_uint64_shift_right(v___y_389_, v___x_390_);
v_fold_392_ = lean_uint64_xor(v___y_389_, v___x_391_);
v___x_393_ = 16ULL;
v___x_394_ = lean_uint64_shift_right(v_fold_392_, v___x_393_);
v___x_395_ = lean_uint64_xor(v_fold_392_, v___x_394_);
v___x_396_ = lean_uint64_to_usize(v___x_395_);
v___x_397_ = lean_usize_of_nat(v___x_387_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_sub(v___x_397_, v___x_398_);
v___x_400_ = lean_usize_land(v___x_396_, v___x_399_);
v_bkt_401_ = lean_array_uget_borrowed(v_buckets_383_, v___x_400_);
v___x_402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_380_, v_bkt_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v_size_x27_404_; lean_object* v___x_405_; lean_object* v_buckets_x27_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v_size_x27_404_ = lean_nat_add(v_size_382_, v___x_403_);
lean_dec(v_size_382_);
lean_inc(v_bkt_401_);
v___x_405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_405_, 0, v_a_380_);
lean_ctor_set(v___x_405_, 1, v_b_381_);
lean_ctor_set(v___x_405_, 2, v_bkt_401_);
v_buckets_x27_406_ = lean_array_uset(v_buckets_383_, v___x_400_, v___x_405_);
v___x_407_ = lean_unsigned_to_nat(4u);
v___x_408_ = lean_nat_mul(v_size_x27_404_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(3u);
v___x_410_ = lean_nat_div(v___x_408_, v___x_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_array_get_size(v_buckets_x27_406_);
v___x_412_ = lean_nat_dec_le(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
if (v___x_412_ == 0)
{
lean_object* v_val_413_; lean_object* v___x_415_; 
v_val_413_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_406_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v_val_413_);
lean_ctor_set(v___x_385_, 0, v_size_x27_404_);
v___x_415_ = v___x_385_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_size_x27_404_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_val_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v___x_418_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v_buckets_x27_406_);
lean_ctor_set(v___x_385_, 0, v_size_x27_404_);
v___x_418_ = v___x_385_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_size_x27_404_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_buckets_x27_406_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_object* v___x_420_; lean_object* v_buckets_x27_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_inc(v_bkt_401_);
v___x_420_ = lean_box(0);
v_buckets_x27_421_ = lean_array_uset(v_buckets_383_, v___x_400_, v___x_420_);
v___x_422_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_380_, v_b_381_, v_bkt_401_);
v___x_423_ = lean_array_uset(v_buckets_x27_421_, v___x_400_, v___x_422_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v___x_423_);
v___x_425_ = v___x_385_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_size_382_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
uint8_t v_stage_u2081_433_; 
v_stage_u2081_433_ = lean_ctor_get_uint8(v_x_430_, sizeof(void*)*2);
if (v_stage_u2081_433_ == 0)
{
lean_object* v_map_u2081_434_; lean_object* v_map_u2082_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_map_u2081_434_ = lean_ctor_get(v_x_430_, 0);
v_map_u2082_435_ = lean_ctor_get(v_x_430_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v_x_430_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_map_u2082_435_);
lean_inc(v_map_u2081_434_);
lean_dec(v_x_430_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_435_, v_x_431_, v_x_432_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_map_u2081_434_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*2, v_stage_u2081_433_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_map_u2081_444_; lean_object* v_map_u2082_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_map_u2081_444_ = lean_ctor_get(v_x_430_, 0);
v_map_u2082_445_ = lean_ctor_get(v_x_430_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v_x_430_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_map_u2082_445_);
lean_inc(v_map_u2081_444_);
lean_dec(v_x_430_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_444_, v_x_431_, v_x_432_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_map_u2082_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*2, v_stage_u2081_433_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v_key_457_; lean_object* v_value_458_; lean_object* v_tail_459_; uint8_t v___x_460_; 
v_key_457_ = lean_ctor_get(v_x_455_, 0);
v_value_458_ = lean_ctor_get(v_x_455_, 1);
v_tail_459_ = lean_ctor_get(v_x_455_, 2);
v___x_460_ = lean_name_eq(v_key_457_, v_a_454_);
if (v___x_460_ == 0)
{
v_x_455_ = v_tail_459_;
goto _start;
}
else
{
lean_object* v___x_462_; 
lean_inc(v_value_458_);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_value_458_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_buckets_468_; lean_object* v___x_469_; uint64_t v___y_471_; 
v_buckets_468_ = lean_ctor_get(v_m_466_, 1);
v___x_469_ = lean_array_get_size(v_buckets_468_);
if (lean_obj_tag(v_a_467_) == 0)
{
uint64_t v___x_485_; 
v___x_485_ = 1723ULL;
v___y_471_ = v___x_485_;
goto v___jp_470_;
}
else
{
uint64_t v_hash_486_; 
v_hash_486_ = lean_ctor_get_uint64(v_a_467_, sizeof(void*)*2);
v___y_471_ = v_hash_486_;
goto v___jp_470_;
}
v___jp_470_:
{
uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v_fold_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_472_ = 32ULL;
v___x_473_ = lean_uint64_shift_right(v___y_471_, v___x_472_);
v_fold_474_ = lean_uint64_xor(v___y_471_, v___x_473_);
v___x_475_ = 16ULL;
v___x_476_ = lean_uint64_shift_right(v_fold_474_, v___x_475_);
v___x_477_ = lean_uint64_xor(v_fold_474_, v___x_476_);
v___x_478_ = lean_uint64_to_usize(v___x_477_);
v___x_479_ = lean_usize_of_nat(v___x_469_);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_sub(v___x_479_, v___x_480_);
v___x_482_ = lean_usize_land(v___x_478_, v___x_481_);
v___x_483_ = lean_array_uget_borrowed(v_buckets_468_, v___x_482_);
v___x_484_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_467_, v___x_483_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_m_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_i_492_, lean_object* v_k_493_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_array_get_size(v_keys_490_);
v___x_495_ = lean_nat_dec_lt(v_i_492_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v_i_492_);
v___x_496_ = lean_box(0);
return v___x_496_;
}
else
{
lean_object* v_k_x27_497_; uint8_t v___x_498_; 
v_k_x27_497_ = lean_array_fget_borrowed(v_keys_490_, v_i_492_);
v___x_498_ = lean_name_eq(v_k_493_, v_k_x27_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_i_492_, v___x_499_);
lean_dec(v_i_492_);
v_i_492_ = v___x_500_;
goto _start;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_array_fget_borrowed(v_vals_491_, v_i_492_);
lean_dec(v_i_492_);
lean_inc(v___x_502_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_504_, lean_object* v_vals_505_, lean_object* v_i_506_, lean_object* v_k_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_504_, v_vals_505_, v_i_506_, v_k_507_);
lean_dec(v_k_507_);
lean_dec_ref(v_vals_505_);
lean_dec_ref(v_keys_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_509_, size_t v_x_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_object* v_es_512_; lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v_j_516_; lean_object* v___x_517_; 
v_es_512_ = lean_ctor_get(v_x_509_, 0);
v___x_513_ = lean_box(2);
v___x_514_ = ((size_t)31ULL);
v___x_515_ = lean_usize_land(v_x_510_, v___x_514_);
v_j_516_ = lean_usize_to_nat(v___x_515_);
v___x_517_ = lean_array_get_borrowed(v___x_513_, v_es_512_, v_j_516_);
lean_dec(v_j_516_);
switch(lean_obj_tag(v___x_517_))
{
case 0:
{
lean_object* v_key_518_; lean_object* v_val_519_; uint8_t v___x_520_; 
v_key_518_ = lean_ctor_get(v___x_517_, 0);
v_val_519_ = lean_ctor_get(v___x_517_, 1);
v___x_520_ = lean_name_eq(v_x_511_, v_key_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v___x_522_; 
lean_inc(v_val_519_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_val_519_);
return v___x_522_;
}
}
case 1:
{
lean_object* v_node_523_; size_t v___x_524_; size_t v___x_525_; 
v_node_523_ = lean_ctor_get(v___x_517_, 0);
v___x_524_ = ((size_t)5ULL);
v___x_525_ = lean_usize_shift_right(v_x_510_, v___x_524_);
v_x_509_ = v_node_523_;
v_x_510_ = v___x_525_;
goto _start;
}
default: 
{
lean_object* v___x_527_; 
v___x_527_ = lean_box(0);
return v___x_527_;
}
}
}
else
{
lean_object* v_ks_528_; lean_object* v_vs_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_ks_528_ = lean_ctor_get(v_x_509_, 0);
v_vs_529_ = lean_ctor_get(v_x_509_, 1);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_528_, v_vs_529_, v___x_530_, v_x_511_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
size_t v_x_1576__boxed_535_; lean_object* v_res_536_; 
v_x_1576__boxed_535_ = lean_unbox_usize(v_x_533_);
lean_dec(v_x_533_);
v_res_536_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_532_, v_x_1576__boxed_535_, v_x_534_);
lean_dec(v_x_534_);
lean_dec_ref(v_x_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint64_t v___y_540_; 
if (lean_obj_tag(v_x_538_) == 0)
{
uint64_t v___x_543_; 
v___x_543_ = 1723ULL;
v___y_540_ = v___x_543_;
goto v___jp_539_;
}
else
{
uint64_t v_hash_544_; 
v_hash_544_ = lean_ctor_get_uint64(v_x_538_, sizeof(void*)*2);
v___y_540_ = v_hash_544_;
goto v___jp_539_;
}
v___jp_539_:
{
size_t v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_uint64_to_usize(v___y_540_);
v___x_542_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_537_, v___x_541_, v_x_538_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_545_, v_x_546_);
lean_dec(v_x_546_);
lean_dec_ref(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
uint8_t v_stage_u2081_550_; 
v_stage_u2081_550_ = lean_ctor_get_uint8(v_x_548_, sizeof(void*)*2);
if (v_stage_u2081_550_ == 0)
{
lean_object* v_map_u2081_551_; lean_object* v_map_u2082_552_; lean_object* v___x_553_; 
v_map_u2081_551_ = lean_ctor_get(v_x_548_, 0);
v_map_u2082_552_ = lean_ctor_get(v_x_548_, 1);
v___x_553_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_552_, v_x_549_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_551_, v_x_549_);
return v___x_554_;
}
else
{
return v___x_553_;
}
}
else
{
lean_object* v_map_u2081_555_; lean_object* v___x_556_; 
v_map_u2081_555_ = lean_ctor_get(v_x_548_, 0);
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_555_, v_x_549_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_557_, v_x_558_);
lean_dec(v_x_558_);
lean_dec_ref(v_x_557_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
uint8_t v___x_562_; 
v___x_562_ = 0;
return v___x_562_;
}
else
{
lean_object* v_head_563_; lean_object* v_tail_564_; uint8_t v___x_565_; 
v_head_563_ = lean_ctor_get(v_x_561_, 0);
v_tail_564_ = lean_ctor_get(v_x_561_, 1);
v___x_565_ = lean_name_eq(v_a_560_, v_head_563_);
if (v___x_565_ == 0)
{
v_x_561_ = v_tail_564_;
goto _start;
}
else
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_567_, lean_object* v_x_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_567_, v_x_568_);
lean_dec(v_x_568_);
lean_dec(v_a_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_571_, lean_object* v_e_572_){
_start:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_590_; 
v_fst_573_ = lean_ctor_get(v_e_572_, 0);
v_snd_574_ = lean_ctor_get(v_e_572_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_e_572_);
if (v_isSharedCheck_590_ == 0)
{
v___x_576_ = v_e_572_;
v_isShared_577_ = v_isSharedCheck_590_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snd_574_);
lean_inc(v_fst_573_);
lean_dec(v_e_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_590_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_571_, v_fst_573_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_box(0);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 1);
lean_ctor_set(v___x_576_, 1, v___x_579_);
lean_ctor_set(v___x_576_, 0, v_snd_574_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_snd_574_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_579_);
v___x_581_ = v_reuseFailAlloc_583_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_571_, v_fst_573_, v___x_581_);
return v___x_582_;
}
}
else
{
lean_object* v_val_584_; uint8_t v___x_585_; 
v_val_584_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v___x_578_, 1);
v___x_585_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_574_, v_val_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_587_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 1);
lean_ctor_set(v___x_576_, 1, v_val_584_);
lean_ctor_set(v___x_576_, 0, v_snd_574_);
v___x_587_ = v___x_576_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_snd_574_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_val_584_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_571_, v_fst_573_, v___x_587_);
return v___x_588_;
}
}
else
{
lean_dec(v_val_584_);
lean_del_object(v___x_576_);
lean_dec(v_snd_574_);
lean_dec(v_fst_573_);
return v_s_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_595_, lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_595_, v_x_596_, v_x_597_);
lean_dec(v_x_597_);
lean_dec_ref(v_x_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_600_, v_x_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_608_, v_x_609_, v_x_610_);
lean_dec(v_x_610_);
lean_dec_ref(v_x_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_612_, lean_object* v_m_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_613_, v_a_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_616_, v_m_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_m_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_621_, v_x_622_, v_x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_a_627_, lean_object* v_b_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_626_, v_a_627_, v_b_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_630_, lean_object* v_x_631_, size_t v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_631_, v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_1741__boxed_639_; lean_object* v_res_640_; 
v_x_1741__boxed_639_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_640_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_635_, v_x_636_, v_x_1741__boxed_639_, v_x_638_);
lean_dec(v_x_638_);
lean_dec_ref(v_x_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_641_, lean_object* v_a_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_645_, lean_object* v_a_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_645_, v_a_646_, v_x_647_);
lean_dec(v_x_647_);
lean_dec(v_a_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, size_t v_x_651_, size_t v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_650_, v_x_651_, v_x_652_, v_x_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
size_t v_x_1757__boxed_662_; size_t v_x_1758__boxed_663_; lean_object* v_res_664_; 
v_x_1757__boxed_662_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_x_1758__boxed_663_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_664_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_656_, v_x_657_, v_x_1757__boxed_662_, v_x_1758__boxed_663_, v_x_660_, v_x_661_);
return v_res_664_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_665_, lean_object* v_a_666_, lean_object* v_x_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_666_, v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_669_, lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_669_, v_a_670_, v_x_671_);
lean_dec(v_x_671_);
lean_dec(v_a_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_674_, lean_object* v_data_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_677_, lean_object* v_a_678_, lean_object* v_b_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_678_, v_b_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_heq_685_, lean_object* v_i_686_, lean_object* v_k_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_683_, v_vals_684_, v_i_686_, v_k_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_689_, lean_object* v_keys_690_, lean_object* v_vals_691_, lean_object* v_heq_692_, lean_object* v_i_693_, lean_object* v_k_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_689_, v_keys_690_, v_vals_691_, v_heq_692_, v_i_693_, v_k_694_);
lean_dec(v_k_694_);
lean_dec_ref(v_vals_691_);
lean_dec_ref(v_keys_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_696_, lean_object* v_n_697_, lean_object* v_k_698_, lean_object* v_v_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_697_, v_k_698_, v_v_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_701_, size_t v_depth_702_, lean_object* v_keys_703_, lean_object* v_vals_704_, lean_object* v_heq_705_, lean_object* v_i_706_, lean_object* v_entries_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_702_, v_keys_703_, v_vals_704_, v_i_706_, v_entries_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_709_, lean_object* v_depth_710_, lean_object* v_keys_711_, lean_object* v_vals_712_, lean_object* v_heq_713_, lean_object* v_i_714_, lean_object* v_entries_715_){
_start:
{
size_t v_depth_boxed_716_; lean_object* v_res_717_; 
v_depth_boxed_716_ = lean_unbox_usize(v_depth_710_);
lean_dec(v_depth_710_);
v_res_717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_709_, v_depth_boxed_716_, v_keys_711_, v_vals_712_, v_heq_713_, v_i_714_, v_entries_715_);
lean_dec_ref(v_vals_712_);
lean_dec_ref(v_keys_711_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_718_, lean_object* v_i_719_, lean_object* v_source_720_, lean_object* v_target_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_719_, v_source_720_, v_target_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_724_, v_x_725_, v_x_726_, v_x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_730_, v_x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_733_){
_start:
{
uint8_t v_stage_u2081_734_; 
v_stage_u2081_734_ = lean_ctor_get_uint8(v_m_733_, sizeof(void*)*2);
if (v_stage_u2081_734_ == 0)
{
return v_m_733_;
}
else
{
lean_object* v_map_u2081_735_; lean_object* v_map_u2082_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_map_u2081_735_ = lean_ctor_get(v_m_733_, 0);
v_map_u2082_736_ = lean_ctor_get(v_m_733_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_m_733_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v_m_733_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_map_u2082_736_);
lean_inc(v_map_u2081_735_);
lean_dec(v_m_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; lean_object* v___x_742_; 
v___x_740_ = 0;
if (v_isShared_739_ == 0)
{
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_map_u2081_735_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_map_u2082_736_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*2, v___x_740_);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_745_, lean_object* v_m_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_array_mk(v_es_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_750_, size_t v_i_751_, size_t v_stop_752_, lean_object* v_b_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_eq(v_i_751_, v_stop_752_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; size_t v___x_757_; size_t v___x_758_; 
v___x_755_ = lean_array_uget_borrowed(v_as_750_, v_i_751_);
lean_inc(v___x_755_);
v___x_756_ = l_Lean_addAliasEntry(v_b_753_, v___x_755_);
v___x_757_ = ((size_t)1ULL);
v___x_758_ = lean_usize_add(v_i_751_, v___x_757_);
v_i_751_ = v___x_758_;
v_b_753_ = v___x_756_;
goto _start;
}
else
{
return v_b_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_760_, lean_object* v_i_761_, lean_object* v_stop_762_, lean_object* v_b_763_){
_start:
{
size_t v_i_boxed_764_; size_t v_stop_boxed_765_; lean_object* v_res_766_; 
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_stop_boxed_765_ = lean_unbox_usize(v_stop_762_);
lean_dec(v_stop_762_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_760_, v_i_boxed_764_, v_stop_boxed_765_, v_b_763_);
lean_dec_ref(v_as_760_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_767_, size_t v_i_768_, size_t v_stop_769_, lean_object* v_b_770_){
_start:
{
lean_object* v___y_772_; uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_eq(v_i_768_, v_stop_769_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_777_ = lean_array_uget_borrowed(v_as_767_, v_i_768_);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_array_get_size(v___x_777_);
v___x_780_ = lean_nat_dec_lt(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
v___y_772_ = v_b_770_;
goto v___jp_771_;
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_779_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_777_, v___x_781_, v___x_782_, v_b_770_);
v___y_772_ = v___x_783_;
goto v___jp_771_;
}
}
else
{
return v_b_770_;
}
v___jp_771_:
{
size_t v___x_773_; size_t v___x_774_; 
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_768_, v___x_773_);
v_i_768_ = v___x_774_;
v_b_770_ = v___y_772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_784_, lean_object* v_i_785_, lean_object* v_stop_786_, lean_object* v_b_787_){
_start:
{
size_t v_i_boxed_788_; size_t v_stop_boxed_789_; lean_object* v_res_790_; 
v_i_boxed_788_ = lean_unbox_usize(v_i_785_);
lean_dec(v_i_785_);
v_stop_boxed_789_ = lean_unbox_usize(v_stop_786_);
lean_dec(v_stop_786_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_784_, v_i_boxed_788_, v_stop_boxed_789_, v_b_787_);
lean_dec_ref(v_as_784_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_791_, lean_object* v_as_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_array_get_size(v_as_792_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
return v_initState_791_;
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_of_nat(v___x_794_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_792_, v___x_796_, v___x_797_, v_initState_791_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_799_, lean_object* v_as_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_799_, v_as_800_);
lean_dec_ref(v_as_800_);
return v_res_801_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_box(0);
v___x_803_ = lean_unsigned_to_nat(16u);
v___x_804_ = lean_mk_array(v___x_803_, v___x_802_);
return v___x_804_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_808_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; 
v___x_811_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_812_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_813_ = 1;
v___x_814_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_811_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*2, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_817_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_816_, v_es_815_);
v___x_818_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_819_);
lean_dec_ref(v_es_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_838_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_841_, lean_object* v_a_842_, lean_object* v_e_843_){
_start:
{
lean_object* v___x_844_; lean_object* v_toEnvExtension_845_; lean_object* v_asyncMode_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_844_ = l_Lean_aliasExtension;
v_toEnvExtension_845_ = lean_ctor_get(v___x_844_, 0);
v_asyncMode_846_ = lean_ctor_get(v_toEnvExtension_845_, 2);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_a_842_);
lean_ctor_set(v___x_847_, 1, v_e_843_);
v___x_848_ = lean_box(0);
v___x_849_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_844_, v_env_841_, v___x_847_, v_asyncMode_846_, v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_853_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_854_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_853_, v___x_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_855_){
_start:
{
lean_object* v___x_856_; lean_object* v_toEnvExtension_857_; lean_object* v_asyncMode_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_856_ = l_Lean_aliasExtension;
v_toEnvExtension_857_ = lean_ctor_get(v___x_856_, 0);
v_asyncMode_858_ = lean_ctor_get(v_toEnvExtension_857_, 2);
v___x_859_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_860_ = lean_box(0);
v___x_861_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_859_, v___x_856_, v_env_855_, v_asyncMode_858_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_862_, uint8_t v_skipProtected_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
if (lean_obj_tag(v_a_864_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref(v_env_862_);
v___x_866_ = l_List_reverse___redArg(v_a_865_);
return v___x_866_;
}
else
{
lean_object* v_head_867_; lean_object* v_tail_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_879_; 
v_head_867_ = lean_ctor_get(v_a_864_, 0);
v_tail_868_ = lean_ctor_get(v_a_864_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_864_);
if (v_isSharedCheck_879_ == 0)
{
v___x_870_ = v_a_864_;
v_isShared_871_ = v_isSharedCheck_879_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_tail_868_);
lean_inc(v_head_867_);
lean_dec(v_a_864_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_879_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; 
lean_inc(v_head_867_);
lean_inc_ref(v_env_862_);
v___x_872_ = l_Lean_isProtected(v_env_862_, v_head_867_);
if (v___x_872_ == 0)
{
if (v_skipProtected_863_ == 0)
{
lean_del_object(v___x_870_);
lean_dec(v_head_867_);
v_a_864_ = v_tail_868_;
goto _start;
}
else
{
lean_object* v___x_875_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v_a_865_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_head_867_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_865_);
v___x_875_ = v_reuseFailAlloc_877_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_a_864_ = v_tail_868_;
v_a_865_ = v___x_875_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_870_);
lean_dec(v_head_867_);
v_a_864_ = v_tail_868_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_880_, lean_object* v_skipProtected_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
uint8_t v_skipProtected_boxed_884_; lean_object* v_res_885_; 
v_skipProtected_boxed_884_ = lean_unbox(v_skipProtected_881_);
v_res_885_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_880_, v_skipProtected_boxed_884_, v_a_882_, v_a_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_886_, lean_object* v_a_887_, uint8_t v_skipProtected_888_){
_start:
{
lean_object* v___x_889_; lean_object* v_toEnvExtension_890_; lean_object* v_asyncMode_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_889_ = l_Lean_aliasExtension;
v_toEnvExtension_890_ = lean_ctor_get(v___x_889_, 0);
v_asyncMode_891_ = lean_ctor_get(v_toEnvExtension_890_, 2);
v___x_892_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_893_ = lean_box(0);
lean_inc_ref(v_env_886_);
v___x_894_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_892_, v___x_889_, v_env_886_, v_asyncMode_891_, v___x_893_);
v___x_895_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_894_, v_a_887_);
lean_dec(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_env_886_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
else
{
if (v_skipProtected_888_ == 0)
{
lean_object* v_val_897_; 
lean_dec_ref(v_env_886_);
v_val_897_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_895_, 1);
return v_val_897_;
}
else
{
lean_object* v_val_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_val_898_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v___x_895_, 1);
v___x_899_ = lean_box(0);
v___x_900_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_886_, v_skipProtected_888_, v_val_898_, v___x_899_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_901_, lean_object* v_a_902_, lean_object* v_skipProtected_903_){
_start:
{
uint8_t v_skipProtected_boxed_904_; lean_object* v_res_905_; 
v_skipProtected_boxed_904_ = lean_unbox(v_skipProtected_903_);
v_res_905_ = l_Lean_getAliases(v_env_901_, v_a_902_, v_skipProtected_boxed_904_);
lean_dec(v_a_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_906_, lean_object* v_as_907_, lean_object* v_a_908_, lean_object* v_es_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_906_, v_es_909_);
if (v___x_910_ == 0)
{
lean_dec(v_a_908_);
return v_as_907_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v_a_908_);
lean_ctor_set(v___x_911_, 1, v_as_907_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_912_, lean_object* v_as_913_, lean_object* v_a_914_, lean_object* v_es_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_getRevAliases___lam__0(v_e_912_, v_as_913_, v_a_914_, v_es_915_);
lean_dec(v_es_915_);
lean_dec(v_e_912_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_917_, lean_object* v_keys_918_, lean_object* v_vals_919_, lean_object* v_i_920_, lean_object* v_acc_921_){
_start:
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = lean_array_get_size(v_keys_918_);
v___x_923_ = lean_nat_dec_lt(v_i_920_, v___x_922_);
if (v___x_923_ == 0)
{
lean_dec(v_i_920_);
lean_dec(v_f_917_);
return v_acc_921_;
}
else
{
lean_object* v_k_924_; lean_object* v_v_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_k_924_ = lean_array_fget_borrowed(v_keys_918_, v_i_920_);
v_v_925_ = lean_array_fget_borrowed(v_vals_919_, v_i_920_);
lean_inc(v_f_917_);
lean_inc(v_v_925_);
lean_inc(v_k_924_);
v___x_926_ = lean_apply_3(v_f_917_, v_acc_921_, v_k_924_, v_v_925_);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_i_920_, v___x_927_);
lean_dec(v_i_920_);
v_i_920_ = v___x_928_;
v_acc_921_ = v___x_926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_i_933_, lean_object* v_acc_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_930_, v_keys_931_, v_vals_932_, v_i_933_, v_acc_934_);
lean_dec_ref(v_vals_932_);
lean_dec_ref(v_keys_931_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_936_, lean_object* v_as_937_, size_t v_i_938_, size_t v_stop_939_, lean_object* v_b_940_){
_start:
{
lean_object* v___y_942_; uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_eq(v_i_938_, v_stop_939_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_array_uget_borrowed(v_as_937_, v_i_938_);
switch(lean_obj_tag(v___x_947_))
{
case 0:
{
lean_object* v_key_948_; lean_object* v_val_949_; lean_object* v___x_950_; 
v_key_948_ = lean_ctor_get(v___x_947_, 0);
v_val_949_ = lean_ctor_get(v___x_947_, 1);
lean_inc(v_f_936_);
lean_inc(v_val_949_);
lean_inc(v_key_948_);
v___x_950_ = lean_apply_3(v_f_936_, v_b_940_, v_key_948_, v_val_949_);
v___y_942_ = v___x_950_;
goto v___jp_941_;
}
case 1:
{
lean_object* v_node_951_; lean_object* v___x_952_; 
v_node_951_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_f_936_);
v___x_952_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_936_, v_node_951_, v_b_940_);
v___y_942_ = v___x_952_;
goto v___jp_941_;
}
default: 
{
v___y_942_ = v_b_940_;
goto v___jp_941_;
}
}
}
else
{
lean_dec(v_f_936_);
return v_b_940_;
}
v___jp_941_:
{
size_t v___x_943_; size_t v___x_944_; 
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_938_, v___x_943_);
v_i_938_ = v___x_944_;
v_b_940_ = v___y_942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v_es_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_es_956_ = lean_ctor_get(v_x_954_, 0);
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_array_get_size(v_es_956_);
v___x_959_ = lean_nat_dec_lt(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_dec(v_f_953_);
return v_x_955_;
}
else
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((size_t)0ULL);
v___x_961_ = lean_usize_of_nat(v___x_958_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_953_, v_es_956_, v___x_960_, v___x_961_, v_x_955_);
return v___x_962_;
}
}
else
{
lean_object* v_ks_963_; lean_object* v_vs_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_ks_963_ = lean_ctor_get(v_x_954_, 0);
v_vs_964_ = lean_ctor_get(v_x_954_, 1);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_953_, v_ks_963_, v_vs_964_, v___x_965_, v_x_955_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_967_, v_x_968_, v_x_969_);
lean_dec_ref(v_x_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_971_, lean_object* v_as_972_, lean_object* v_i_973_, lean_object* v_stop_974_, lean_object* v_b_975_){
_start:
{
size_t v_i_boxed_976_; size_t v_stop_boxed_977_; lean_object* v_res_978_; 
v_i_boxed_976_ = lean_unbox_usize(v_i_973_);
lean_dec(v_i_973_);
v_stop_boxed_977_ = lean_unbox_usize(v_stop_974_);
lean_dec(v_stop_974_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_971_, v_as_972_, v_i_boxed_976_, v_stop_boxed_977_, v_b_975_);
lean_dec_ref(v_as_972_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_979_, lean_object* v_x1_980_, lean_object* v_x2_981_, lean_object* v_x3_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_apply_3(v_f_979_, v_x1_980_, v_x2_981_, v_x3_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_984_, lean_object* v_f_985_, lean_object* v_init_986_){
_start:
{
lean_object* v___f_987_; lean_object* v___x_988_; 
v___f_987_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_987_, 0, v_f_985_);
v___x_988_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_987_, v_map_984_, v_init_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_989_, lean_object* v_f_990_, lean_object* v_init_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_989_, v_f_990_, v_init_991_);
lean_dec_ref(v_map_989_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
lean_dec(v_f_993_);
return v_x_994_;
}
else
{
lean_object* v_key_996_; lean_object* v_value_997_; lean_object* v_tail_998_; lean_object* v___x_999_; 
v_key_996_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_key_996_);
v_value_997_ = lean_ctor_get(v_x_995_, 1);
lean_inc(v_value_997_);
v_tail_998_ = lean_ctor_get(v_x_995_, 2);
lean_inc(v_tail_998_);
lean_dec_ref_known(v_x_995_, 3);
lean_inc(v_f_993_);
v___x_999_ = lean_apply_3(v_f_993_, v_x_994_, v_key_996_, v_value_997_);
v_x_994_ = v___x_999_;
v_x_995_ = v_tail_998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1001_, lean_object* v_as_1002_, size_t v_i_1003_, size_t v_stop_1004_, lean_object* v_b_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_1003_, v_stop_1004_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; 
v___x_1007_ = lean_array_uget_borrowed(v_as_1002_, v_i_1003_);
lean_inc(v___x_1007_);
lean_inc(v_f_1001_);
v___x_1008_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1001_, v_b_1005_, v___x_1007_);
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1003_, v___x_1009_);
v_i_1003_ = v___x_1010_;
v_b_1005_ = v___x_1008_;
goto _start;
}
else
{
lean_dec(v_f_1001_);
return v_b_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1012_, lean_object* v_as_1013_, lean_object* v_i_1014_, lean_object* v_stop_1015_, lean_object* v_b_1016_){
_start:
{
size_t v_i_boxed_1017_; size_t v_stop_boxed_1018_; lean_object* v_res_1019_; 
v_i_boxed_1017_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_stop_boxed_1018_ = lean_unbox_usize(v_stop_1015_);
lean_dec(v_stop_1015_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1012_, v_as_1013_, v_i_boxed_1017_, v_stop_boxed_1018_, v_b_1016_);
lean_dec_ref(v_as_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1020_, lean_object* v_init_1021_, lean_object* v_m_1022_){
_start:
{
lean_object* v_map_u2081_1023_; lean_object* v_map_u2082_1024_; lean_object* v_buckets_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_map_u2081_1023_ = lean_ctor_get(v_m_1022_, 0);
v_map_u2082_1024_ = lean_ctor_get(v_m_1022_, 1);
v_buckets_1025_ = lean_ctor_get(v_map_u2081_1023_, 1);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_array_get_size(v_buckets_1025_);
v___x_1028_ = lean_nat_dec_lt(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1024_, v_f_1020_, v_init_1021_);
return v___x_1029_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = lean_usize_of_nat(v___x_1027_);
lean_inc(v_f_1020_);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1020_, v_buckets_1025_, v___x_1030_, v___x_1031_, v_init_1021_);
v___x_1033_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1024_, v_f_1020_, v___x_1032_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1034_, lean_object* v_init_1035_, lean_object* v_m_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1034_, v_init_1035_, v_m_1036_);
lean_dec_ref(v_m_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1038_, lean_object* v_e_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v_toEnvExtension_1041_; lean_object* v_asyncMode_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1040_ = l_Lean_aliasExtension;
v_toEnvExtension_1041_ = lean_ctor_get(v___x_1040_, 0);
v_asyncMode_1042_ = lean_ctor_get(v_toEnvExtension_1041_, 2);
v___f_1043_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1043_, 0, v_e_1039_);
v___x_1044_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_box(0);
v___x_1047_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1044_, v___x_1040_, v_env_1038_, v_asyncMode_1042_, v___x_1046_);
v___x_1048_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1043_, v___x_1045_, v___x_1047_);
lean_dec(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1049_, lean_object* v_00_u03c3_1050_, lean_object* v_f_1051_, lean_object* v_init_1052_, lean_object* v_m_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1051_, v_init_1052_, v_m_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1055_, lean_object* v_00_u03c3_1056_, lean_object* v_f_1057_, lean_object* v_init_1058_, lean_object* v_m_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1055_, v_00_u03c3_1056_, v_f_1057_, v_init_1058_, v_m_1059_);
lean_dec_ref(v_m_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1061_, lean_object* v_00_u03c3_1062_, lean_object* v_f_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1063_, v_x_1064_, v_x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_map_1069_, lean_object* v_f_1070_, lean_object* v_init_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1069_, v_f_1070_, v_init_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_map_1075_, lean_object* v_f_1076_, lean_object* v_init_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1073_, v_00_u03b2_1074_, v_map_1075_, v_f_1076_, v_init_1077_);
lean_dec_ref(v_map_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1079_, lean_object* v_00_u03c3_1080_, lean_object* v_f_1081_, lean_object* v_as_1082_, size_t v_i_1083_, size_t v_stop_1084_, lean_object* v_b_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1081_, v_as_1082_, v_i_1083_, v_stop_1084_, v_b_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_00_u03c3_1088_, lean_object* v_f_1089_, lean_object* v_as_1090_, lean_object* v_i_1091_, lean_object* v_stop_1092_, lean_object* v_b_1093_){
_start:
{
size_t v_i_boxed_1094_; size_t v_stop_boxed_1095_; lean_object* v_res_1096_; 
v_i_boxed_1094_ = lean_unbox_usize(v_i_1091_);
lean_dec(v_i_1091_);
v_stop_boxed_1095_ = lean_unbox_usize(v_stop_1092_);
lean_dec(v_stop_1092_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1087_, v_00_u03c3_1088_, v_f_1089_, v_as_1090_, v_i_boxed_1094_, v_stop_boxed_1095_, v_b_1093_);
lean_dec_ref(v_as_1090_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1097_, lean_object* v_f_1098_, lean_object* v_init_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1098_, v_map_1097_, v_init_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1101_, lean_object* v_f_1102_, lean_object* v_init_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1101_, v_f_1102_, v_init_1103_);
lean_dec_ref(v_map_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_map_1107_, lean_object* v_f_1108_, lean_object* v_init_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1108_, v_map_1107_, v_init_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_map_1113_, lean_object* v_f_1114_, lean_object* v_init_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1111_, v_00_u03b2_1112_, v_map_1113_, v_f_1114_, v_init_1115_);
lean_dec_ref(v_map_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1117_, lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_f_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1120_, v_x_1121_, v_x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1124_, lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_f_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1124_, v_00_u03b1_1125_, v_00_u03b2_1126_, v_f_1127_, v_x_1128_, v_x_1129_);
lean_dec_ref(v_x_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1131_, lean_object* v_00_u03b2_1132_, lean_object* v_00_u03c3_1133_, lean_object* v_f_1134_, lean_object* v_as_1135_, size_t v_i_1136_, size_t v_stop_1137_, lean_object* v_b_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1134_, v_as_1135_, v_i_1136_, v_stop_1137_, v_b_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_00_u03c3_1142_, lean_object* v_f_1143_, lean_object* v_as_1144_, lean_object* v_i_1145_, lean_object* v_stop_1146_, lean_object* v_b_1147_){
_start:
{
size_t v_i_boxed_1148_; size_t v_stop_boxed_1149_; lean_object* v_res_1150_; 
v_i_boxed_1148_ = lean_unbox_usize(v_i_1145_);
lean_dec(v_i_1145_);
v_stop_boxed_1149_ = lean_unbox_usize(v_stop_1146_);
lean_dec(v_stop_1146_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1140_, v_00_u03b2_1141_, v_00_u03c3_1142_, v_f_1143_, v_as_1144_, v_i_boxed_1148_, v_stop_boxed_1149_, v_b_1147_);
lean_dec_ref(v_as_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1151_, lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_f_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_acc_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1154_, v_keys_1155_, v_vals_1156_, v_i_1158_, v_acc_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1161_, lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_f_1164_, lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_heq_1167_, lean_object* v_i_1168_, lean_object* v_acc_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1161_, v_00_u03b1_1162_, v_00_u03b2_1163_, v_f_1164_, v_keys_1165_, v_vals_1166_, v_heq_1167_, v_i_1168_, v_acc_1169_);
lean_dec_ref(v_vals_1166_);
lean_dec_ref(v_keys_1165_);
return v_res_1170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1171_, lean_object* v_declName_1172_){
_start:
{
uint8_t v___y_1174_; uint8_t v___x_1177_; 
v___x_1177_ = l_Lean_Environment_containsOnBranch(v_env_1171_, v_declName_1172_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1178_; 
lean_inc(v_declName_1172_);
lean_inc_ref(v_env_1171_);
v___x_1178_ = lean_is_reserved_name(v_env_1171_, v_declName_1172_);
v___y_1174_ = v___x_1178_;
goto v___jp_1173_;
}
else
{
v___y_1174_ = v___x_1177_;
goto v___jp_1173_;
}
v___jp_1173_:
{
if (v___y_1174_ == 0)
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 1;
v___x_1176_ = l_Lean_Environment_contains(v_env_1171_, v_declName_1172_, v___x_1175_);
return v___x_1176_;
}
else
{
lean_dec(v_declName_1172_);
lean_dec_ref(v_env_1171_);
return v___y_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1179_, lean_object* v_declName_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1179_, v_declName_1180_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1183_, lean_object* v_decl_1184_, lean_object* v_ref_1185_){
_start:
{
lean_object* v_defValue_1187_; lean_object* v_descr_1188_; lean_object* v_deprecation_x3f_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_defValue_1187_ = lean_ctor_get(v_decl_1184_, 0);
v_descr_1188_ = lean_ctor_get(v_decl_1184_, 1);
v_deprecation_x3f_1189_ = lean_ctor_get(v_decl_1184_, 2);
v___x_1190_ = lean_alloc_ctor(1, 0, 1);
v___x_1191_ = lean_unbox(v_defValue_1187_);
lean_ctor_set_uint8(v___x_1190_, 0, v___x_1191_);
lean_inc(v_deprecation_x3f_1189_);
lean_inc_ref(v_descr_1188_);
lean_inc_n(v_name_1183_, 2);
v___x_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1192_, 0, v_name_1183_);
lean_ctor_set(v___x_1192_, 1, v_ref_1185_);
lean_ctor_set(v___x_1192_, 2, v___x_1190_);
lean_ctor_set(v___x_1192_, 3, v_descr_1188_);
lean_ctor_set(v___x_1192_, 4, v_deprecation_x3f_1189_);
v___x_1193_ = lean_register_option(v_name_1183_, v___x_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1193_, 0);
lean_dec(v_unused_1202_);
v___x_1195_ = v___x_1193_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v___x_1193_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_inc(v_defValue_1187_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_name_1183_);
lean_ctor_set(v___x_1197_, 1, v_defValue_1187_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_name_1183_);
v_a_1203_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1193_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1193_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1211_, lean_object* v_decl_1212_, lean_object* v_ref_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1211_, v_decl_1212_, v_ref_1213_);
lean_dec_ref(v_decl_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1235_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1236_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1237_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1234_, v___x_1235_, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1259_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1260_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1261_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1258_, v___x_1259_, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1263_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1264_, lean_object* v_opt_1265_){
_start:
{
lean_object* v_name_1266_; lean_object* v_defValue_1267_; lean_object* v_map_1268_; lean_object* v___x_1269_; 
v_name_1266_ = lean_ctor_get(v_opt_1265_, 0);
v_defValue_1267_ = lean_ctor_get(v_opt_1265_, 1);
v_map_1268_ = lean_ctor_get(v_opts_1264_, 0);
v___x_1269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1268_, v_name_1266_);
if (lean_obj_tag(v___x_1269_) == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_unbox(v_defValue_1267_);
return v___x_1270_;
}
else
{
lean_object* v_val_1271_; 
v_val_1271_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v___x_1269_, 1);
if (lean_obj_tag(v_val_1271_) == 1)
{
uint8_t v_v_1272_; 
v_v_1272_ = lean_ctor_get_uint8(v_val_1271_, 0);
lean_dec_ref_known(v_val_1271_, 0);
return v_v_1272_;
}
else
{
uint8_t v___x_1273_; 
lean_dec(v_val_1271_);
v___x_1273_ = lean_unbox(v_defValue_1267_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1274_, lean_object* v_opt_1275_){
_start:
{
uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1274_, v_opt_1275_);
lean_dec_ref(v_opt_1275_);
lean_dec_ref(v_opts_1274_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1281_, lean_object* v_env_1282_, lean_object* v_as_1283_, size_t v_sz_1284_, size_t v_i_1285_, lean_object* v_b_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_usize_dec_lt(v_i_1285_, v_sz_1284_);
if (v___x_1287_ == 0)
{
lean_dec_ref(v_env_1282_);
lean_dec(v_declName_1281_);
lean_inc_ref(v_b_1286_);
return v_b_1286_;
}
else
{
lean_object* v_a_1288_; lean_object* v_toImport_1289_; lean_object* v_module_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_a_1288_ = lean_array_uget_borrowed(v_as_1283_, v_i_1285_);
v_toImport_1289_ = lean_ctor_get(v_a_1288_, 0);
v_module_1290_ = lean_ctor_get(v_toImport_1289_, 0);
v___x_1291_ = lean_box(0);
lean_inc(v_declName_1281_);
lean_inc(v_module_1290_);
v___x_1292_ = l_Lean_mkPrivateNameCore(v_module_1290_, v_declName_1281_);
lean_inc(v___x_1292_);
lean_inc_ref(v_env_1282_);
v___x_1293_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1282_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; 
lean_dec(v___x_1292_);
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1285_, v___x_1295_);
v_i_1285_ = v___x_1296_;
v_b_1286_ = v___x_1294_;
goto _start;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_env_1282_);
lean_dec(v_declName_1281_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1292_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1291_);
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1301_, lean_object* v_env_1302_, lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1301_, v_env_1302_, v_as_1303_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1306_);
lean_dec_ref(v_b_1306_);
lean_dec_ref(v_as_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1310_, lean_object* v_opts_1311_, lean_object* v_declName_1312_){
_start:
{
uint8_t v_isExporting_1328_; 
v_isExporting_1328_ = lean_ctor_get_uint8(v_env_1310_, sizeof(void*)*8);
if (v_isExporting_1328_ == 0)
{
goto v___jp_1313_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1330_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1311_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec(v_declName_1312_);
lean_dec_ref(v_env_1310_);
v___x_1331_ = lean_box(0);
return v___x_1331_;
}
else
{
goto v___jp_1313_;
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
lean_inc(v_declName_1312_);
v___x_1314_ = l_Lean_mkPrivateName(v_env_1310_, v_declName_1312_);
lean_inc(v___x_1314_);
lean_inc_ref(v_env_1310_);
v___x_1315_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1310_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v_isModule_1317_; 
lean_dec(v___x_1314_);
v___x_1316_ = l_Lean_Environment_header(v_env_1310_);
v_isModule_1317_ = lean_ctor_get_uint8(v___x_1316_, sizeof(void*)*7 + 4);
if (v_isModule_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1316_);
lean_dec(v_declName_1312_);
lean_dec_ref(v_env_1310_);
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
else
{
lean_object* v_importAllModules_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v_fst_1325_; 
v_importAllModules_1319_ = lean_ctor_get(v___x_1316_, 5);
lean_inc_ref(v_importAllModules_1319_);
lean_dec_ref(v___x_1316_);
v___x_1320_ = lean_box(0);
v___x_1321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1322_ = lean_array_size(v_importAllModules_1319_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1312_, v_env_1310_, v_importAllModules_1319_, v_sz_1322_, v___x_1323_, v___x_1321_);
lean_dec_ref(v_importAllModules_1319_);
v_fst_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_fst_1325_);
lean_dec_ref(v___x_1324_);
if (lean_obj_tag(v_fst_1325_) == 0)
{
return v___x_1320_;
}
else
{
lean_object* v_val_1326_; 
v_val_1326_ = lean_ctor_get(v_fst_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v_fst_1325_, 1);
return v_val_1326_;
}
}
}
else
{
lean_object* v___x_1327_; 
lean_dec(v_declName_1312_);
lean_dec_ref(v_env_1310_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1314_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1332_, lean_object* v_opts_1333_, lean_object* v_declName_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1332_, v_opts_1333_, v_declName_1334_);
lean_dec_ref(v_opts_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1336_, lean_object* v_opts_1337_, lean_object* v_ns_1338_, lean_object* v_id_1339_){
_start:
{
lean_object* v_resolvedId_1340_; uint8_t v___x_1341_; lean_object* v_resolvedIds_1342_; 
lean_inc(v_id_1339_);
v_resolvedId_1340_ = l_Lean_Name_append(v_ns_1338_, v_id_1339_);
v___x_1341_ = l_Lean_Name_isAtomic(v_id_1339_);
lean_dec(v_id_1339_);
lean_inc_ref(v_env_1336_);
v_resolvedIds_1342_ = l_Lean_getAliases(v_env_1336_, v_resolvedId_1340_, v___x_1341_);
if (v___x_1341_ == 0)
{
goto v___jp_1343_;
}
else
{
uint8_t v___x_1349_; 
lean_inc(v_resolvedId_1340_);
lean_inc_ref(v_env_1336_);
v___x_1349_ = l_Lean_isProtected(v_env_1336_, v_resolvedId_1340_);
if (v___x_1349_ == 0)
{
goto v___jp_1343_;
}
else
{
lean_dec(v_resolvedId_1340_);
lean_dec_ref(v_env_1336_);
return v_resolvedIds_1342_;
}
}
v___jp_1343_:
{
uint8_t v___x_1344_; 
lean_inc(v_resolvedId_1340_);
lean_inc_ref(v_env_1336_);
v___x_1344_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1336_, v_resolvedId_1340_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1336_, v_opts_1337_, v_resolvedId_1340_);
if (lean_obj_tag(v___x_1345_) == 1)
{
lean_object* v_val_1346_; lean_object* v___x_1347_; 
v_val_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_val_1346_);
lean_ctor_set(v___x_1347_, 1, v_resolvedIds_1342_);
return v___x_1347_;
}
else
{
lean_dec(v___x_1345_);
return v_resolvedIds_1342_;
}
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v_env_1336_);
v___x_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_resolvedId_1340_);
lean_ctor_set(v___x_1348_, 1, v_resolvedIds_1342_);
return v___x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1350_, lean_object* v_opts_1351_, lean_object* v_ns_1352_, lean_object* v_id_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1350_, v_opts_1351_, v_ns_1352_, v_id_1353_);
lean_dec_ref(v_opts_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1355_, lean_object* v_opts_1356_, lean_object* v_id_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 1)
{
lean_object* v_pre_1359_; lean_object* v___x_1360_; 
v_pre_1359_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_pre_1359_);
lean_inc(v_id_1357_);
lean_inc_ref(v_env_1355_);
v___x_1360_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1355_, v_opts_1356_, v_x_1358_, v_id_1357_);
if (lean_obj_tag(v___x_1360_) == 0)
{
v_x_1358_ = v_pre_1359_;
goto _start;
}
else
{
lean_dec(v_pre_1359_);
lean_dec(v_id_1357_);
lean_dec_ref(v_env_1355_);
return v___x_1360_;
}
}
else
{
lean_object* v___x_1362_; 
lean_dec(v_x_1358_);
lean_dec(v_id_1357_);
lean_dec_ref(v_env_1355_);
v___x_1362_ = lean_box(0);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1363_, lean_object* v_opts_1364_, lean_object* v_id_1365_, lean_object* v_x_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1363_, v_opts_1364_, v_id_1365_, v_x_1366_);
lean_dec_ref(v_opts_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1368_, lean_object* v_opts_1369_, lean_object* v_id_1370_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = l_Lean_Name_isAtomic(v_id_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_resolvedId_1374_; uint8_t v___x_1375_; 
v___x_1372_ = l_Lean_rootNamespace;
v___x_1373_ = lean_box(0);
v_resolvedId_1374_ = l_Lean_Name_replacePrefix(v_id_1370_, v___x_1372_, v___x_1373_);
lean_inc(v_resolvedId_1374_);
lean_inc_ref(v_env_1368_);
v___x_1375_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1368_, v_resolvedId_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1368_, v_opts_1369_, v_resolvedId_1374_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; 
lean_dec_ref(v_env_1368_);
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_resolvedId_1374_);
return v___x_1377_;
}
}
else
{
lean_object* v___x_1378_; 
lean_dec(v_id_1370_);
lean_dec_ref(v_env_1368_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1379_, lean_object* v_opts_1380_, lean_object* v_id_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1379_, v_opts_1380_, v_id_1381_);
lean_dec_ref(v_opts_1380_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1383_, lean_object* v_opts_1384_, lean_object* v_id_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
lean_dec(v_id_1385_);
lean_dec_ref(v_env_1383_);
return v_x_1387_;
}
else
{
lean_object* v_head_1388_; 
v_head_1388_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_head_1388_);
if (lean_obj_tag(v_head_1388_) == 0)
{
lean_object* v_tail_1389_; lean_object* v_ns_1390_; lean_object* v_except_1391_; uint8_t v___x_1392_; 
v_tail_1389_ = lean_ctor_get(v_x_1386_, 1);
lean_inc(v_tail_1389_);
lean_dec_ref_known(v_x_1386_, 2);
v_ns_1390_ = lean_ctor_get(v_head_1388_, 0);
lean_inc(v_ns_1390_);
v_except_1391_ = lean_ctor_get(v_head_1388_, 1);
lean_inc(v_except_1391_);
lean_dec_ref_known(v_head_1388_, 2);
v___x_1392_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1385_, v_except_1391_);
lean_dec(v_except_1391_);
if (v___x_1392_ == 0)
{
lean_object* v_newResolvedIds_1393_; lean_object* v___x_1394_; 
lean_inc(v_id_1385_);
lean_inc_ref(v_env_1383_);
v_newResolvedIds_1393_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1383_, v_opts_1384_, v_ns_1390_, v_id_1385_);
v___x_1394_ = l_List_appendTR___redArg(v_newResolvedIds_1393_, v_x_1387_);
v_x_1386_ = v_tail_1389_;
v_x_1387_ = v___x_1394_;
goto _start;
}
else
{
lean_dec(v_ns_1390_);
v_x_1386_ = v_tail_1389_;
goto _start;
}
}
else
{
lean_object* v_tail_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1417_; 
v_tail_1397_ = lean_ctor_get(v_x_1386_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_x_1386_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_x_1386_, 0);
lean_dec(v_unused_1418_);
v___x_1399_ = v_x_1386_;
v_isShared_1400_ = v_isSharedCheck_1417_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_tail_1397_);
lean_dec(v_x_1386_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1417_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_id_1401_; lean_object* v_declName_1402_; uint8_t v___x_1403_; 
v_id_1401_ = lean_ctor_get(v_head_1388_, 0);
lean_inc(v_id_1401_);
v_declName_1402_ = lean_ctor_get(v_head_1388_, 1);
lean_inc(v_declName_1402_);
lean_dec_ref_known(v_head_1388_, 2);
v___x_1403_ = lean_name_eq(v_id_1401_, v_id_1385_);
if (v___x_1403_ == 0)
{
uint8_t v___x_1404_; 
v___x_1404_ = l_Lean_Name_isPrefixOf(v_id_1401_, v_id_1385_);
if (v___x_1404_ == 0)
{
lean_dec(v_declName_1402_);
lean_dec(v_id_1401_);
lean_del_object(v___x_1399_);
v_x_1386_ = v_tail_1397_;
goto _start;
}
else
{
lean_object* v_candidate_1406_; uint8_t v___x_1407_; 
lean_inc(v_id_1385_);
v_candidate_1406_ = l_Lean_Name_replacePrefix(v_id_1385_, v_id_1401_, v_declName_1402_);
lean_dec(v_declName_1402_);
lean_dec(v_id_1401_);
lean_inc(v_candidate_1406_);
lean_inc_ref(v_env_1383_);
v___x_1407_ = l_Lean_Environment_contains(v_env_1383_, v_candidate_1406_, v___x_1404_);
if (v___x_1407_ == 0)
{
lean_dec(v_candidate_1406_);
lean_del_object(v___x_1399_);
v_x_1386_ = v_tail_1397_;
goto _start;
}
else
{
lean_object* v___x_1410_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v_x_1387_);
lean_ctor_set(v___x_1399_, 0, v_candidate_1406_);
v___x_1410_ = v___x_1399_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_candidate_1406_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_x_1387_);
v___x_1410_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v_x_1386_ = v_tail_1397_;
v_x_1387_ = v___x_1410_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1414_; 
lean_dec(v_id_1401_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v_x_1387_);
lean_ctor_set(v___x_1399_, 0, v_declName_1402_);
v___x_1414_ = v___x_1399_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_declName_1402_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_x_1387_);
v___x_1414_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
v_x_1386_ = v_tail_1397_;
v_x_1387_ = v___x_1414_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1419_, lean_object* v_opts_1420_, lean_object* v_id_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1419_, v_opts_1420_, v_id_1421_, v_x_1422_, v_x_1423_);
lean_dec_ref(v_opts_1420_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1426_){
_start:
{
lean_object* v___f_1427_; lean_object* v___x_1428_; 
v___f_1427_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1428_ = l_List_eraseDupsBy___redArg(v___f_1427_, v_as_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
if (lean_obj_tag(v_a_1430_) == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_projs_1429_);
v___x_1432_ = l_List_reverse___redArg(v_a_1431_);
return v___x_1432_;
}
else
{
lean_object* v_head_1433_; lean_object* v_tail_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1443_; 
v_head_1433_ = lean_ctor_get(v_a_1430_, 0);
v_tail_1434_ = lean_ctor_get(v_a_1430_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_a_1430_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1436_ = v_a_1430_;
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_tail_1434_);
lean_inc(v_head_1433_);
lean_dec(v_a_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_inc(v_projs_1429_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_head_1433_);
lean_ctor_set(v___x_1438_, 1, v_projs_1429_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_a_1431_);
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_a_1431_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v_a_1430_ = v_tail_1434_;
v_a_1431_ = v___x_1440_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1444_, lean_object* v_opts_1445_, lean_object* v_ns_1446_, lean_object* v_openDecls_1447_, lean_object* v_extractionResult_1448_, lean_object* v_id_1449_, lean_object* v_projs_1450_){
_start:
{
if (lean_obj_tag(v_id_1449_) == 1)
{
lean_object* v_pre_1451_; lean_object* v_str_1452_; lean_object* v_imported_1453_; lean_object* v_ctx_1454_; lean_object* v_scopes_1455_; lean_object* v___x_1456_; lean_object* v_id_1457_; lean_object* v___y_1459_; lean_object* v___x_1469_; lean_object* v___y_1471_; 
v_pre_1451_ = lean_ctor_get(v_id_1449_, 0);
lean_inc(v_pre_1451_);
v_str_1452_ = lean_ctor_get(v_id_1449_, 1);
lean_inc_ref(v_str_1452_);
v_imported_1453_ = lean_ctor_get(v_extractionResult_1448_, 1);
v_ctx_1454_ = lean_ctor_get(v_extractionResult_1448_, 2);
v_scopes_1455_ = lean_ctor_get(v_extractionResult_1448_, 3);
lean_inc(v_scopes_1455_);
lean_inc(v_ctx_1454_);
lean_inc(v_imported_1453_);
v___x_1456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1456_, 0, v_id_1449_);
lean_ctor_set(v___x_1456_, 1, v_imported_1453_);
lean_ctor_set(v___x_1456_, 2, v_ctx_1454_);
lean_ctor_set(v___x_1456_, 3, v_scopes_1455_);
v_id_1457_ = l_Lean_MacroScopesView_review(v___x_1456_);
lean_inc(v_ns_1446_);
lean_inc(v_id_1457_);
lean_inc_ref(v_env_1444_);
v___x_1469_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1444_, v_opts_1445_, v_id_1457_, v_ns_1446_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1476_; 
lean_inc(v_id_1457_);
lean_inc_ref(v_env_1444_);
v___x_1476_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1444_, v_opts_1445_, v_id_1457_);
if (lean_obj_tag(v___x_1476_) == 0)
{
uint8_t v___x_1477_; 
lean_inc(v_id_1457_);
lean_inc_ref(v_env_1444_);
v___x_1477_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1444_, v_id_1457_);
if (v___x_1477_ == 0)
{
v___y_1471_ = v___x_1469_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1478_; 
lean_inc(v_id_1457_);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_id_1457_);
lean_ctor_set(v___x_1478_, 1, v___x_1469_);
v___y_1471_ = v___x_1478_;
goto v___jp_1470_;
}
}
else
{
lean_object* v_val_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec(v_id_1457_);
lean_dec_ref(v_str_1452_);
lean_dec(v_pre_1451_);
lean_dec(v_openDecls_1447_);
lean_dec(v_ns_1446_);
lean_dec_ref(v_env_1444_);
v_val_1479_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_val_1479_);
lean_ctor_set(v___x_1480_, 1, v_projs_1450_);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
return v___x_1482_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v_id_1457_);
lean_dec_ref(v_str_1452_);
lean_dec(v_pre_1451_);
lean_dec(v_openDecls_1447_);
lean_dec(v_ns_1446_);
lean_dec_ref(v_env_1444_);
v___x_1483_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1469_);
v___x_1484_ = lean_box(0);
v___x_1485_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1450_, v___x_1483_, v___x_1484_);
return v___x_1485_;
}
v___jp_1458_:
{
lean_object* v_resolvedIds_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v_resolvedIds_1463_; 
lean_inc(v_openDecls_1447_);
lean_inc(v_id_1457_);
lean_inc_ref_n(v_env_1444_, 2);
v_resolvedIds_1460_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1444_, v_opts_1445_, v_id_1457_, v_openDecls_1447_, v___y_1459_);
v___x_1461_ = l_Lean_Name_isAtomic(v_id_1457_);
v___x_1462_ = l_Lean_getAliases(v_env_1444_, v_id_1457_, v___x_1461_);
lean_dec(v_id_1457_);
v_resolvedIds_1463_ = l_List_appendTR___redArg(v___x_1462_, v_resolvedIds_1460_);
if (lean_obj_tag(v_resolvedIds_1463_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_str_1452_);
lean_ctor_set(v___x_1464_, 1, v_projs_1450_);
v_id_1449_ = v_pre_1451_;
v_projs_1450_ = v___x_1464_;
goto _start;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v_str_1452_);
lean_dec(v_pre_1451_);
lean_dec(v_openDecls_1447_);
lean_dec(v_ns_1446_);
lean_dec_ref(v_env_1444_);
v___x_1466_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1463_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1450_, v___x_1466_, v___x_1467_);
return v___x_1468_;
}
}
v___jp_1470_:
{
lean_object* v___x_1472_; 
lean_inc(v_id_1457_);
lean_inc_ref(v_env_1444_);
v___x_1472_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1444_, v_opts_1445_, v_id_1457_);
if (lean_obj_tag(v___x_1472_) == 1)
{
lean_object* v_val_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_val_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_val_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1469_);
v___x_1475_ = l_List_appendTR___redArg(v___x_1474_, v___y_1471_);
v___y_1459_ = v___x_1475_;
goto v___jp_1458_;
}
else
{
lean_dec(v___x_1472_);
lean_dec(v___x_1469_);
v___y_1459_ = v___y_1471_;
goto v___jp_1458_;
}
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_projs_1450_);
lean_dec(v_id_1449_);
lean_dec(v_openDecls_1447_);
lean_dec(v_ns_1446_);
lean_dec_ref(v_env_1444_);
v___x_1486_ = lean_box(0);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1487_, lean_object* v_opts_1488_, lean_object* v_ns_1489_, lean_object* v_openDecls_1490_, lean_object* v_extractionResult_1491_, lean_object* v_id_1492_, lean_object* v_projs_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1487_, v_opts_1488_, v_ns_1489_, v_openDecls_1490_, v_extractionResult_1491_, v_id_1492_, v_projs_1493_);
lean_dec_ref(v_extractionResult_1491_);
lean_dec_ref(v_opts_1488_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1495_, lean_object* v_opts_1496_, lean_object* v_ns_1497_, lean_object* v_openDecls_1498_, lean_object* v_id_1499_){
_start:
{
lean_object* v_extractionResult_1500_; lean_object* v_name_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_extractionResult_1500_ = l_Lean_extractMacroScopes(v_id_1499_);
v_name_1501_ = lean_ctor_get(v_extractionResult_1500_, 0);
lean_inc(v_name_1501_);
v___x_1502_ = lean_box(0);
v___x_1503_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1495_, v_opts_1496_, v_ns_1497_, v_openDecls_1498_, v_extractionResult_1500_, v_name_1501_, v___x_1502_);
lean_dec_ref(v_extractionResult_1500_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1504_, lean_object* v_opts_1505_, lean_object* v_ns_1506_, lean_object* v_openDecls_1507_, lean_object* v_id_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_ResolveName_resolveGlobalName(v_env_1504_, v_opts_1505_, v_ns_1506_, v_openDecls_1507_, v_id_1508_);
lean_dec_ref(v_opts_1505_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_panic_fn_borrowed(v___x_1511_, v_msg_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1516_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1517_ = lean_unsigned_to_nat(9u);
v___x_1518_ = lean_unsigned_to_nat(230u);
v___x_1519_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1520_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1521_ = l_mkPanicMessageWithDecl(v___x_1520_, v___x_1519_, v___x_1518_, v___x_1517_, v___x_1516_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1522_, lean_object* v_n_1523_, lean_object* v_ns_1524_){
_start:
{
switch(lean_obj_tag(v_ns_1524_))
{
case 1:
{
lean_object* v_pre_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_pre_1525_ = lean_ctor_get(v_ns_1524_, 0);
lean_inc(v_pre_1525_);
lean_inc(v_n_1523_);
v___x_1526_ = l_Lean_Name_append(v_ns_1524_, v_n_1523_);
lean_inc_ref(v_env_1522_);
v___x_1527_ = l_Lean_Environment_isNamespace(v_env_1522_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec(v___x_1526_);
v_ns_1524_ = v_pre_1525_;
goto _start;
}
else
{
lean_object* v___x_1529_; 
lean_dec(v_pre_1525_);
lean_dec(v_n_1523_);
lean_dec_ref(v_env_1522_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
return v___x_1529_;
}
}
case 0:
{
lean_object* v___x_1530_; lean_object* v_n_1531_; uint8_t v___x_1532_; 
v___x_1530_ = l_Lean_rootNamespace;
v_n_1531_ = l_Lean_Name_replacePrefix(v_n_1523_, v___x_1530_, v_ns_1524_);
v___x_1532_ = l_Lean_Environment_isNamespace(v_env_1522_, v_n_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec(v_n_1531_);
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_n_1531_);
return v___x_1534_;
}
}
default: 
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_ns_1524_);
lean_dec(v_n_1523_);
lean_dec_ref(v_env_1522_);
v___x_1535_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1536_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1535_);
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1537_, lean_object* v_n_1538_, lean_object* v_x_1539_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
lean_object* v___x_1540_; 
lean_dec(v_n_1538_);
lean_dec_ref(v_env_1537_);
v___x_1540_ = lean_box(0);
return v___x_1540_;
}
else
{
lean_object* v_head_1541_; 
v_head_1541_ = lean_ctor_get(v_x_1539_, 0);
if (lean_obj_tag(v_head_1541_) == 0)
{
lean_object* v_tail_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1559_; 
lean_inc_ref(v_head_1541_);
v_tail_1542_ = lean_ctor_get(v_x_1539_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_x_1539_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_x_1539_, 0);
lean_dec(v_unused_1560_);
v___x_1544_ = v_x_1539_;
v_isShared_1545_ = v_isSharedCheck_1559_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_tail_1542_);
lean_dec(v_x_1539_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1559_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_ns_1546_; lean_object* v_except_1547_; lean_object* v___x_1548_; uint8_t v___y_1550_; uint8_t v___x_1556_; 
v_ns_1546_ = lean_ctor_get(v_head_1541_, 0);
lean_inc(v_ns_1546_);
v_except_1547_ = lean_ctor_get(v_head_1541_, 1);
lean_inc(v_except_1547_);
lean_dec_ref_known(v_head_1541_, 2);
lean_inc(v_n_1538_);
v___x_1548_ = l_Lean_Name_append(v_ns_1546_, v_n_1538_);
lean_inc_ref(v_env_1537_);
v___x_1556_ = l_Lean_Environment_isNamespace(v_env_1537_, v___x_1548_);
if (v___x_1556_ == 0)
{
lean_dec(v_except_1547_);
v___y_1550_ = v___x_1556_;
goto v___jp_1549_;
}
else
{
uint8_t v___x_1557_; 
v___x_1557_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1538_, v_except_1547_);
lean_dec(v_except_1547_);
if (v___x_1557_ == 0)
{
v___y_1550_ = v___x_1556_;
goto v___jp_1549_;
}
else
{
lean_dec(v___x_1548_);
lean_del_object(v___x_1544_);
v_x_1539_ = v_tail_1542_;
goto _start;
}
}
v___jp_1549_:
{
if (v___y_1550_ == 0)
{
lean_dec(v___x_1548_);
lean_del_object(v___x_1544_);
v_x_1539_ = v_tail_1542_;
goto _start;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1537_, v_n_1538_, v_tail_1542_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___x_1552_);
lean_ctor_set(v___x_1544_, 0, v___x_1548_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
else
{
lean_object* v_tail_1561_; 
v_tail_1561_ = lean_ctor_get(v_x_1539_, 1);
lean_inc(v_tail_1561_);
lean_dec_ref_known(v_x_1539_, 2);
v_x_1539_ = v_tail_1561_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1563_, lean_object* v_ns_1564_, lean_object* v_openDecls_1565_, lean_object* v_id_1566_){
_start:
{
lean_object* v___x_1567_; 
lean_inc(v_id_1566_);
lean_inc_ref(v_env_1563_);
v___x_1567_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1563_, v_id_1566_, v_ns_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1563_, v_id_1566_, v_openDecls_1565_);
return v___x_1568_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_val_1569_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1569_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1570_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1563_, v_id_1566_, v_openDecls_1565_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_val_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1572_, lean_object* v_inst_1573_){
_start:
{
lean_object* v_getCurrNamespace_1574_; lean_object* v_getOpenDecls_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1584_; 
v_getCurrNamespace_1574_ = lean_ctor_get(v_inst_1573_, 0);
v_getOpenDecls_1575_ = lean_ctor_get(v_inst_1573_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_inst_1573_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1577_ = v_inst_1573_;
v_isShared_1578_ = v_isSharedCheck_1584_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_getOpenDecls_1575_);
lean_inc(v_getCurrNamespace_1574_);
lean_dec(v_inst_1573_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1584_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_inc(v_inst_1572_);
v___x_1579_ = lean_apply_2(v_inst_1572_, lean_box(0), v_getCurrNamespace_1574_);
v___x_1580_ = lean_apply_2(v_inst_1572_, lean_box(0), v_getOpenDecls_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___x_1580_);
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1585_, lean_object* v_n_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1587_, v_inst_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1596_, lean_object* v_toPure_1597_, lean_object* v_id_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, uint8_t v_____do__lift_1603_){
_start:
{
uint8_t v_isExporting_1607_; 
v_isExporting_1607_ = lean_ctor_get_uint8(v_____do__lift_1596_, sizeof(void*)*8);
if (v_isExporting_1607_ == 0)
{
lean_dec(v_inst_1602_);
lean_dec(v_inst_1601_);
lean_dec_ref(v_inst_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec(v_id_1598_);
goto v___jp_1604_;
}
else
{
uint8_t v___x_1608_; 
v___x_1608_ = l_Lean_isPrivateName(v_id_1598_);
if (v___x_1608_ == 0)
{
lean_dec(v_inst_1602_);
lean_dec(v_inst_1601_);
lean_dec_ref(v_inst_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec(v_id_1598_);
goto v___jp_1604_;
}
else
{
if (v_____do__lift_1603_ == 0)
{
lean_dec(v_inst_1602_);
lean_dec(v_inst_1601_);
lean_dec_ref(v_inst_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec(v_id_1598_);
goto v___jp_1604_;
}
else
{
lean_object* v___x_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v_toPure_1597_);
v___x_1609_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1610_ = 0;
v___x_1611_ = l_Lean_MessageData_ofConstName(v_id_1598_, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1609_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_logWarning___redArg(v_inst_1599_, v_inst_1600_, v_inst_1601_, v_inst_1602_, v___x_1614_);
return v___x_1615_;
}
}
}
v___jp_1604_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_apply_2(v_toPure_1597_, lean_box(0), v___x_1605_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1616_, lean_object* v_toPure_1617_, lean_object* v_id_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_____do__lift_1623_){
_start:
{
uint8_t v_____do__lift_197__boxed_1624_; lean_object* v_res_1625_; 
v_____do__lift_197__boxed_1624_ = lean_unbox(v_____do__lift_1623_);
v_res_1625_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1616_, v_toPure_1617_, v_id_1618_, v_inst_1619_, v_inst_1620_, v_inst_1621_, v_inst_1622_, v_____do__lift_197__boxed_1624_);
lean_dec_ref(v_____do__lift_1616_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1626_, lean_object* v_id_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v___x_1632_, lean_object* v_toBind_1633_, lean_object* v_____do__lift_1634_){
_start:
{
lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_inc(v_inst_1631_);
lean_inc_ref(v_inst_1628_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1635_, 0, v_____do__lift_1634_);
lean_closure_set(v___f_1635_, 1, v_toPure_1626_);
lean_closure_set(v___f_1635_, 2, v_id_1627_);
lean_closure_set(v___f_1635_, 3, v_inst_1628_);
lean_closure_set(v___f_1635_, 4, v_inst_1629_);
lean_closure_set(v___f_1635_, 5, v_inst_1630_);
lean_closure_set(v___f_1635_, 6, v_inst_1631_);
v___x_1636_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1637_ = l_Lean_Option_getM___redArg(v_inst_1628_, v_inst_1631_, v___x_1632_, v___x_1636_);
v___x_1638_ = lean_apply_4(v_toBind_1633_, lean_box(0), lean_box(0), v___x_1637_, v___f_1635_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_id_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v_toApplicative_1646_; lean_object* v_toBind_1647_; lean_object* v_getEnv_1648_; lean_object* v_toPure_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; 
v___x_1645_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1646_ = lean_ctor_get(v_inst_1639_, 0);
v_toBind_1647_ = lean_ctor_get(v_inst_1639_, 1);
lean_inc_n(v_toBind_1647_, 2);
v_getEnv_1648_ = lean_ctor_get(v_inst_1640_, 0);
lean_inc(v_getEnv_1648_);
lean_dec_ref(v_inst_1640_);
v_toPure_1649_ = lean_ctor_get(v_toApplicative_1646_, 1);
lean_inc(v_toPure_1649_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1650_, 0, v_toPure_1649_);
lean_closure_set(v___f_1650_, 1, v_id_1644_);
lean_closure_set(v___f_1650_, 2, v_inst_1639_);
lean_closure_set(v___f_1650_, 3, v_inst_1642_);
lean_closure_set(v___f_1650_, 4, v_inst_1643_);
lean_closure_set(v___f_1650_, 5, v_inst_1641_);
lean_closure_set(v___f_1650_, 6, v___x_1645_);
lean_closure_set(v___f_1650_, 7, v_toBind_1647_);
v___x_1651_ = lean_apply_4(v_toBind_1647_, lean_box(0), lean_box(0), v_getEnv_1648_, v___f_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_id_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_inst_1657_, v_id_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1660_, lean_object* v_n_1661_, lean_object* v_toPure_1662_, uint8_t v___y_1663_, uint8_t v___x_1664_, lean_object* v_____r_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1660_, v_n_1661_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_box(v___y_1663_);
v___x_1668_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1667_);
return v___x_1668_;
}
else
{
lean_object* v_val_1669_; lean_object* v___x_1670_; uint8_t v_isModule_1671_; 
v_val_1669_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1669_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1670_ = l_Lean_Environment_header(v_env_1660_);
v_isModule_1671_ = lean_ctor_get_uint8(v___x_1670_, sizeof(void*)*7 + 4);
if (v_isModule_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec_ref(v___x_1670_);
lean_dec(v_val_1669_);
v___x_1672_ = lean_box(v___x_1664_);
v___x_1673_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1672_);
return v___x_1673_;
}
else
{
lean_object* v_modules_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_modules_1674_ = lean_ctor_get(v___x_1670_, 3);
lean_inc_ref(v_modules_1674_);
lean_dec_ref(v___x_1670_);
v___x_1675_ = lean_array_get_size(v_modules_1674_);
v___x_1676_ = lean_nat_dec_lt(v_val_1669_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v_modules_1674_);
lean_dec(v_val_1669_);
v___x_1677_ = lean_box(v_isModule_1671_);
v___x_1678_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1677_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; lean_object* v_toImport_1680_; uint8_t v_importAll_1681_; 
v___x_1679_ = lean_array_fget(v_modules_1674_, v_val_1669_);
lean_dec(v_val_1669_);
lean_dec_ref(v_modules_1674_);
v_toImport_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_ref(v_toImport_1680_);
lean_dec(v___x_1679_);
v_importAll_1681_ = lean_ctor_get_uint8(v_toImport_1680_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1680_);
if (v_importAll_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_box(v_isModule_1671_);
v___x_1683_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1682_);
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_box(v___y_1663_);
v___x_1685_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1684_);
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1686_, lean_object* v_n_1687_, lean_object* v_toPure_1688_, lean_object* v___y_1689_, lean_object* v___x_1690_, lean_object* v_____r_1691_){
_start:
{
uint8_t v___y_384__boxed_1692_; uint8_t v___x_385__boxed_1693_; lean_object* v_res_1694_; 
v___y_384__boxed_1692_ = lean_unbox(v___y_1689_);
v___x_385__boxed_1693_ = lean_unbox(v___x_1690_);
v_res_1694_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1686_, v_n_1687_, v_toPure_1688_, v___y_384__boxed_1692_, v___x_385__boxed_1693_, v_____r_1691_);
lean_dec(v_n_1687_);
lean_dec_ref(v_env_1686_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1695_, lean_object* v_n_1696_, lean_object* v_toPure_1697_, uint8_t v___x_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_toBind_1704_, uint8_t v___y_1705_, uint8_t v_____do__lift_1706_){
_start:
{
uint8_t v___y_1708_; uint8_t v_isExporting_1714_; 
v_isExporting_1714_ = lean_ctor_get_uint8(v_env_1695_, sizeof(void*)*8);
if (v_isExporting_1714_ == 0)
{
v___y_1708_ = v___y_1705_;
goto v___jp_1707_;
}
else
{
if (v_____do__lift_1706_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec(v_toBind_1704_);
lean_dec(v_inst_1703_);
lean_dec_ref(v_inst_1702_);
lean_dec(v_inst_1701_);
lean_dec_ref(v_inst_1700_);
lean_dec_ref(v_inst_1699_);
lean_dec(v_n_1696_);
lean_dec_ref(v_env_1695_);
v___x_1715_ = lean_box(v___x_1698_);
v___x_1716_ = lean_apply_2(v_toPure_1697_, lean_box(0), v___x_1715_);
return v___x_1716_;
}
else
{
v___y_1708_ = v___y_1705_;
goto v___jp_1707_;
}
}
v___jp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1709_ = lean_box(v___y_1708_);
v___x_1710_ = lean_box(v___x_1698_);
lean_inc(v_n_1696_);
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1711_, 0, v_env_1695_);
lean_closure_set(v___f_1711_, 1, v_n_1696_);
lean_closure_set(v___f_1711_, 2, v_toPure_1697_);
lean_closure_set(v___f_1711_, 3, v___x_1709_);
lean_closure_set(v___f_1711_, 4, v___x_1710_);
v___x_1712_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1699_, v_inst_1700_, v_inst_1701_, v_inst_1702_, v_inst_1703_, v_n_1696_);
v___x_1713_ = lean_apply_4(v_toBind_1704_, lean_box(0), lean_box(0), v___x_1712_, v___f_1711_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1717_, lean_object* v_n_1718_, lean_object* v_toPure_1719_, lean_object* v___x_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_toBind_1726_, lean_object* v___y_1727_, lean_object* v_____do__lift_1728_){
_start:
{
uint8_t v___x_425__boxed_1729_; uint8_t v___y_431__boxed_1730_; uint8_t v_____do__lift_432__boxed_1731_; lean_object* v_res_1732_; 
v___x_425__boxed_1729_ = lean_unbox(v___x_1720_);
v___y_431__boxed_1730_ = lean_unbox(v___y_1727_);
v_____do__lift_432__boxed_1731_ = lean_unbox(v_____do__lift_1728_);
v_res_1732_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1717_, v_n_1718_, v_toPure_1719_, v___x_425__boxed_1729_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_inst_1724_, v_inst_1725_, v_toBind_1726_, v___y_431__boxed_1730_, v_____do__lift_432__boxed_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1733_, lean_object* v_toPure_1734_, uint8_t v___x_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_toBind_1741_, uint8_t v___y_1742_, lean_object* v___x_1743_, lean_object* v_env_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1745_ = lean_box(v___x_1735_);
v___x_1746_ = lean_box(v___y_1742_);
lean_inc(v_toBind_1741_);
lean_inc(v_inst_1738_);
lean_inc_ref(v_inst_1736_);
v___f_1747_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1747_, 0, v_env_1744_);
lean_closure_set(v___f_1747_, 1, v_n_1733_);
lean_closure_set(v___f_1747_, 2, v_toPure_1734_);
lean_closure_set(v___f_1747_, 3, v___x_1745_);
lean_closure_set(v___f_1747_, 4, v_inst_1736_);
lean_closure_set(v___f_1747_, 5, v_inst_1737_);
lean_closure_set(v___f_1747_, 6, v_inst_1738_);
lean_closure_set(v___f_1747_, 7, v_inst_1739_);
lean_closure_set(v___f_1747_, 8, v_inst_1740_);
lean_closure_set(v___f_1747_, 9, v_toBind_1741_);
lean_closure_set(v___f_1747_, 10, v___x_1746_);
v___x_1748_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1749_ = l_Lean_Option_getM___redArg(v_inst_1736_, v_inst_1738_, v___x_1743_, v___x_1748_);
v___x_1750_ = lean_apply_4(v_toBind_1741_, lean_box(0), lean_box(0), v___x_1749_, v___f_1747_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1751_, lean_object* v_toPure_1752_, lean_object* v___x_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_toBind_1759_, lean_object* v___y_1760_, lean_object* v___x_1761_, lean_object* v_env_1762_){
_start:
{
uint8_t v___x_467__boxed_1763_; uint8_t v___y_473__boxed_1764_; lean_object* v_res_1765_; 
v___x_467__boxed_1763_ = lean_unbox(v___x_1753_);
v___y_473__boxed_1764_ = lean_unbox(v___y_1760_);
v_res_1765_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1751_, v_toPure_1752_, v___x_467__boxed_1763_, v_inst_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v_inst_1758_, v_toBind_1759_, v___y_473__boxed_1764_, v___x_1761_, v_env_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_inst_1770_, lean_object* v_n_1771_){
_start:
{
lean_object* v___x_1772_; uint8_t v___y_1774_; uint8_t v___x_1789_; 
v___x_1772_ = l_Lean_KVMap_instValueBool;
v___x_1789_ = l_Lean_isPrivateName(v_n_1771_);
if (v___x_1789_ == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = 1;
v___y_1774_ = v___x_1790_;
goto v___jp_1773_;
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
v___y_1774_ = v___x_1791_;
goto v___jp_1773_;
}
v___jp_1773_:
{
if (v___y_1774_ == 0)
{
lean_object* v_toApplicative_1775_; lean_object* v_toBind_1776_; lean_object* v_toPure_1777_; lean_object* v_getEnv_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; 
v_toApplicative_1775_ = lean_ctor_get(v_inst_1768_, 0);
v_toBind_1776_ = lean_ctor_get(v_inst_1768_, 1);
lean_inc_n(v_toBind_1776_, 2);
v_toPure_1777_ = lean_ctor_get(v_toApplicative_1775_, 1);
lean_inc(v_toPure_1777_);
v_getEnv_1778_ = lean_ctor_get(v_inst_1769_, 0);
lean_inc(v_getEnv_1778_);
v___x_1779_ = 1;
v___x_1780_ = lean_box(v___x_1779_);
v___x_1781_ = lean_box(v___y_1774_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1782_, 0, v_n_1771_);
lean_closure_set(v___f_1782_, 1, v_toPure_1777_);
lean_closure_set(v___f_1782_, 2, v___x_1780_);
lean_closure_set(v___f_1782_, 3, v_inst_1768_);
lean_closure_set(v___f_1782_, 4, v_inst_1769_);
lean_closure_set(v___f_1782_, 5, v_inst_1770_);
lean_closure_set(v___f_1782_, 6, v_inst_1766_);
lean_closure_set(v___f_1782_, 7, v_inst_1767_);
lean_closure_set(v___f_1782_, 8, v_toBind_1776_);
lean_closure_set(v___f_1782_, 9, v___x_1781_);
lean_closure_set(v___f_1782_, 10, v___x_1772_);
v___x_1783_ = lean_apply_4(v_toBind_1776_, lean_box(0), lean_box(0), v_getEnv_1778_, v___f_1782_);
return v___x_1783_;
}
else
{
lean_object* v_toApplicative_1784_; lean_object* v_toPure_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_toApplicative_1784_ = lean_ctor_get(v_inst_1768_, 0);
lean_inc_ref(v_toApplicative_1784_);
lean_dec(v_n_1771_);
lean_dec(v_inst_1770_);
lean_dec_ref(v_inst_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
v_toPure_1785_ = lean_ctor_get(v_toApplicative_1784_, 1);
lean_inc(v_toPure_1785_);
lean_dec_ref(v_toApplicative_1784_);
v___x_1786_ = 0;
v___x_1787_ = lean_box(v___x_1786_);
v___x_1788_ = lean_apply_2(v_toPure_1785_, lean_box(0), v___x_1787_);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_n_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_inst_1797_, v_n_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1800_){
_start:
{
lean_object* v_fst_1801_; uint8_t v___x_1802_; 
v_fst_1801_ = lean_ctor_get(v_x_1800_, 0);
v___x_1802_ = l_Lean_isPrivateName(v_fst_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1803_);
lean_dec_ref(v_x_1803_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1806_, lean_object* v_res_1807_, lean_object* v_____r_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_apply_2(v_toPure_1806_, lean_box(0), v_res_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1810_, lean_object* v_toPure_1811_, lean_object* v_res_1812_, lean_object* v___f_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_toBind_1819_, lean_object* v___f_1820_, lean_object* v_____do__lift_1821_){
_start:
{
if (v_enableLog_1810_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v___f_1820_);
lean_dec(v_toBind_1819_);
lean_dec(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
lean_dec(v_inst_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v___f_1813_);
v___x_1822_ = lean_apply_2(v_toPure_1811_, lean_box(0), v_res_1812_);
return v___x_1822_;
}
else
{
uint8_t v_isExporting_1823_; 
v_isExporting_1823_ = lean_ctor_get_uint8(v_____do__lift_1821_, sizeof(void*)*8);
if (v_isExporting_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v___f_1820_);
lean_dec(v_toBind_1819_);
lean_dec(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
lean_dec(v_inst_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v___f_1813_);
v___x_1824_ = lean_apply_2(v_toPure_1811_, lean_box(0), v_res_1812_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; 
lean_inc(v_res_1812_);
v___x_1825_ = l_List_find_x3f___redArg(v___f_1813_, v_res_1812_);
if (lean_obj_tag(v___x_1825_) == 1)
{
lean_object* v_val_1826_; lean_object* v_fst_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v_res_1812_);
lean_dec(v_toPure_1811_);
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v_fst_1827_ = lean_ctor_get(v_val_1826_, 0);
lean_inc(v_fst_1827_);
lean_dec(v_val_1826_);
v___x_1828_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1814_, v_inst_1815_, v_inst_1816_, v_inst_1817_, v_inst_1818_, v_fst_1827_);
v___x_1829_ = lean_apply_4(v_toBind_1819_, lean_box(0), lean_box(0), v___x_1828_, v___f_1820_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; 
lean_dec(v___x_1825_);
lean_dec(v___f_1820_);
lean_dec(v_toBind_1819_);
lean_dec(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
lean_dec(v_inst_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
v___x_1830_ = lean_apply_2(v_toPure_1811_, lean_box(0), v_res_1812_);
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1831_, lean_object* v_toPure_1832_, lean_object* v_res_1833_, lean_object* v___f_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_toBind_1840_, lean_object* v___f_1841_, lean_object* v_____do__lift_1842_){
_start:
{
uint8_t v_enableLog_boxed_1843_; lean_object* v_res_1844_; 
v_enableLog_boxed_1843_ = lean_unbox(v_enableLog_1831_);
v_res_1844_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1843_, v_toPure_1832_, v_res_1833_, v___f_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_inst_1838_, v_inst_1839_, v_toBind_1840_, v___f_1841_, v_____do__lift_1842_);
lean_dec_ref(v_____do__lift_1842_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1845_, lean_object* v_____do__lift_1846_, lean_object* v_____do__lift_1847_, lean_object* v_id_1848_, lean_object* v_toPure_1849_, uint8_t v_enableLog_1850_, lean_object* v___f_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_toBind_1857_, lean_object* v_getEnv_1858_, lean_object* v_____do__lift_1859_){
_start:
{
lean_object* v_res_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; 
v_res_1860_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1845_, v_____do__lift_1846_, v_____do__lift_1847_, v_____do__lift_1859_, v_id_1848_);
lean_inc(v_res_1860_);
lean_inc(v_toPure_1849_);
v___f_1861_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1861_, 0, v_toPure_1849_);
lean_closure_set(v___f_1861_, 1, v_res_1860_);
v___x_1862_ = lean_box(v_enableLog_1850_);
lean_inc(v_toBind_1857_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1863_, 0, v___x_1862_);
lean_closure_set(v___f_1863_, 1, v_toPure_1849_);
lean_closure_set(v___f_1863_, 2, v_res_1860_);
lean_closure_set(v___f_1863_, 3, v___f_1851_);
lean_closure_set(v___f_1863_, 4, v_inst_1852_);
lean_closure_set(v___f_1863_, 5, v_inst_1853_);
lean_closure_set(v___f_1863_, 6, v_inst_1854_);
lean_closure_set(v___f_1863_, 7, v_inst_1855_);
lean_closure_set(v___f_1863_, 8, v_inst_1856_);
lean_closure_set(v___f_1863_, 9, v_toBind_1857_);
lean_closure_set(v___f_1863_, 10, v___f_1861_);
v___x_1864_ = lean_apply_4(v_toBind_1857_, lean_box(0), lean_box(0), v_getEnv_1858_, v___f_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1865_, lean_object* v_____do__lift_1866_, lean_object* v_____do__lift_1867_, lean_object* v_id_1868_, lean_object* v_toPure_1869_, lean_object* v_enableLog_1870_, lean_object* v___f_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_toBind_1877_, lean_object* v_getEnv_1878_, lean_object* v_____do__lift_1879_){
_start:
{
uint8_t v_enableLog_boxed_1880_; lean_object* v_res_1881_; 
v_enableLog_boxed_1880_ = lean_unbox(v_enableLog_1870_);
v_res_1881_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1865_, v_____do__lift_1866_, v_____do__lift_1867_, v_id_1868_, v_toPure_1869_, v_enableLog_boxed_1880_, v___f_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_inst_1875_, v_inst_1876_, v_toBind_1877_, v_getEnv_1878_, v_____do__lift_1879_);
lean_dec_ref(v_____do__lift_1866_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1882_, lean_object* v_____do__lift_1883_, lean_object* v_id_1884_, lean_object* v_toPure_1885_, uint8_t v_enableLog_1886_, lean_object* v___f_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_toBind_1893_, lean_object* v_getEnv_1894_, lean_object* v_getOpenDecls_1895_, lean_object* v_____do__lift_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_box(v_enableLog_1886_);
lean_inc(v_toBind_1893_);
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1898_, 0, v_____do__lift_1882_);
lean_closure_set(v___f_1898_, 1, v_____do__lift_1883_);
lean_closure_set(v___f_1898_, 2, v_____do__lift_1896_);
lean_closure_set(v___f_1898_, 3, v_id_1884_);
lean_closure_set(v___f_1898_, 4, v_toPure_1885_);
lean_closure_set(v___f_1898_, 5, v___x_1897_);
lean_closure_set(v___f_1898_, 6, v___f_1887_);
lean_closure_set(v___f_1898_, 7, v_inst_1888_);
lean_closure_set(v___f_1898_, 8, v_inst_1889_);
lean_closure_set(v___f_1898_, 9, v_inst_1890_);
lean_closure_set(v___f_1898_, 10, v_inst_1891_);
lean_closure_set(v___f_1898_, 11, v_inst_1892_);
lean_closure_set(v___f_1898_, 12, v_toBind_1893_);
lean_closure_set(v___f_1898_, 13, v_getEnv_1894_);
v___x_1899_ = lean_apply_4(v_toBind_1893_, lean_box(0), lean_box(0), v_getOpenDecls_1895_, v___f_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1900_, lean_object* v_____do__lift_1901_, lean_object* v_id_1902_, lean_object* v_toPure_1903_, lean_object* v_enableLog_1904_, lean_object* v___f_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_toBind_1911_, lean_object* v_getEnv_1912_, lean_object* v_getOpenDecls_1913_, lean_object* v_____do__lift_1914_){
_start:
{
uint8_t v_enableLog_boxed_1915_; lean_object* v_res_1916_; 
v_enableLog_boxed_1915_ = lean_unbox(v_enableLog_1904_);
v_res_1916_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1900_, v_____do__lift_1901_, v_id_1902_, v_toPure_1903_, v_enableLog_boxed_1915_, v___f_1905_, v_inst_1906_, v_inst_1907_, v_inst_1908_, v_inst_1909_, v_inst_1910_, v_toBind_1911_, v_getEnv_1912_, v_getOpenDecls_1913_, v_____do__lift_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1917_, lean_object* v_____do__lift_1918_, lean_object* v_id_1919_, lean_object* v_toPure_1920_, uint8_t v_enableLog_1921_, lean_object* v___f_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_toBind_1928_, lean_object* v_getEnv_1929_, lean_object* v_____do__lift_1930_){
_start:
{
lean_object* v_getCurrNamespace_1931_; lean_object* v_getOpenDecls_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v_getCurrNamespace_1931_ = lean_ctor_get(v_inst_1917_, 0);
lean_inc(v_getCurrNamespace_1931_);
v_getOpenDecls_1932_ = lean_ctor_get(v_inst_1917_, 1);
lean_inc(v_getOpenDecls_1932_);
lean_dec_ref(v_inst_1917_);
v___x_1933_ = lean_box(v_enableLog_1921_);
lean_inc(v_toBind_1928_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1934_, 0, v_____do__lift_1918_);
lean_closure_set(v___f_1934_, 1, v_____do__lift_1930_);
lean_closure_set(v___f_1934_, 2, v_id_1919_);
lean_closure_set(v___f_1934_, 3, v_toPure_1920_);
lean_closure_set(v___f_1934_, 4, v___x_1933_);
lean_closure_set(v___f_1934_, 5, v___f_1922_);
lean_closure_set(v___f_1934_, 6, v_inst_1923_);
lean_closure_set(v___f_1934_, 7, v_inst_1924_);
lean_closure_set(v___f_1934_, 8, v_inst_1925_);
lean_closure_set(v___f_1934_, 9, v_inst_1926_);
lean_closure_set(v___f_1934_, 10, v_inst_1927_);
lean_closure_set(v___f_1934_, 11, v_toBind_1928_);
lean_closure_set(v___f_1934_, 12, v_getEnv_1929_);
lean_closure_set(v___f_1934_, 13, v_getOpenDecls_1932_);
v___x_1935_ = lean_apply_4(v_toBind_1928_, lean_box(0), lean_box(0), v_getCurrNamespace_1931_, v___f_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1936_, lean_object* v_____do__lift_1937_, lean_object* v_id_1938_, lean_object* v_toPure_1939_, lean_object* v_enableLog_1940_, lean_object* v___f_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_toBind_1947_, lean_object* v_getEnv_1948_, lean_object* v_____do__lift_1949_){
_start:
{
uint8_t v_enableLog_boxed_1950_; lean_object* v_res_1951_; 
v_enableLog_boxed_1950_ = lean_unbox(v_enableLog_1940_);
v_res_1951_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1936_, v_____do__lift_1937_, v_id_1938_, v_toPure_1939_, v_enableLog_boxed_1950_, v___f_1941_, v_inst_1942_, v_inst_1943_, v_inst_1944_, v_inst_1945_, v_inst_1946_, v_toBind_1947_, v_getEnv_1948_, v_____do__lift_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1952_, lean_object* v_id_1953_, lean_object* v_toPure_1954_, uint8_t v_enableLog_1955_, lean_object* v___f_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_toBind_1962_, lean_object* v_getEnv_1963_, lean_object* v_____do__lift_1964_){
_start:
{
lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; 
v___x_1965_ = lean_box(v_enableLog_1955_);
lean_inc(v_toBind_1962_);
lean_inc(v_inst_1959_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1966_, 0, v_inst_1952_);
lean_closure_set(v___f_1966_, 1, v_____do__lift_1964_);
lean_closure_set(v___f_1966_, 2, v_id_1953_);
lean_closure_set(v___f_1966_, 3, v_toPure_1954_);
lean_closure_set(v___f_1966_, 4, v___x_1965_);
lean_closure_set(v___f_1966_, 5, v___f_1956_);
lean_closure_set(v___f_1966_, 6, v_inst_1957_);
lean_closure_set(v___f_1966_, 7, v_inst_1958_);
lean_closure_set(v___f_1966_, 8, v_inst_1959_);
lean_closure_set(v___f_1966_, 9, v_inst_1960_);
lean_closure_set(v___f_1966_, 10, v_inst_1961_);
lean_closure_set(v___f_1966_, 11, v_toBind_1962_);
lean_closure_set(v___f_1966_, 12, v_getEnv_1963_);
v___x_1967_ = lean_apply_4(v_toBind_1962_, lean_box(0), lean_box(0), v_inst_1959_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1968_, lean_object* v_id_1969_, lean_object* v_toPure_1970_, lean_object* v_enableLog_1971_, lean_object* v___f_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_toBind_1978_, lean_object* v_getEnv_1979_, lean_object* v_____do__lift_1980_){
_start:
{
uint8_t v_enableLog_boxed_1981_; lean_object* v_res_1982_; 
v_enableLog_boxed_1981_ = lean_unbox(v_enableLog_1971_);
v_res_1982_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1968_, v_id_1969_, v_toPure_1970_, v_enableLog_boxed_1981_, v___f_1972_, v_inst_1973_, v_inst_1974_, v_inst_1975_, v_inst_1976_, v_inst_1977_, v_toBind_1978_, v_getEnv_1979_, v_____do__lift_1980_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_id_1990_, uint8_t v_enableLog_1991_){
_start:
{
lean_object* v_toApplicative_1992_; lean_object* v_toBind_1993_; lean_object* v_getEnv_1994_; lean_object* v_toPure_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; lean_object* v___f_1998_; lean_object* v___x_1999_; 
v_toApplicative_1992_ = lean_ctor_get(v_inst_1984_, 0);
v_toBind_1993_ = lean_ctor_get(v_inst_1984_, 1);
lean_inc_n(v_toBind_1993_, 2);
v_getEnv_1994_ = lean_ctor_get(v_inst_1986_, 0);
lean_inc_n(v_getEnv_1994_, 2);
v_toPure_1995_ = lean_ctor_get(v_toApplicative_1992_, 1);
lean_inc(v_toPure_1995_);
v___f_1996_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_1997_ = lean_box(v_enableLog_1991_);
v___f_1998_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1998_, 0, v_inst_1985_);
lean_closure_set(v___f_1998_, 1, v_id_1990_);
lean_closure_set(v___f_1998_, 2, v_toPure_1995_);
lean_closure_set(v___f_1998_, 3, v___x_1997_);
lean_closure_set(v___f_1998_, 4, v___f_1996_);
lean_closure_set(v___f_1998_, 5, v_inst_1984_);
lean_closure_set(v___f_1998_, 6, v_inst_1986_);
lean_closure_set(v___f_1998_, 7, v_inst_1987_);
lean_closure_set(v___f_1998_, 8, v_inst_1988_);
lean_closure_set(v___f_1998_, 9, v_inst_1989_);
lean_closure_set(v___f_1998_, 10, v_toBind_1993_);
lean_closure_set(v___f_1998_, 11, v_getEnv_1994_);
v___x_1999_ = lean_apply_4(v_toBind_1993_, lean_box(0), lean_box(0), v_getEnv_1994_, v___f_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_id_2006_, lean_object* v_enableLog_2007_){
_start:
{
uint8_t v_enableLog_boxed_2008_; lean_object* v_res_2009_; 
v_enableLog_boxed_2008_ = lean_unbox(v_enableLog_2007_);
v_res_2009_ = l_Lean_resolveGlobalName___redArg(v_inst_2000_, v_inst_2001_, v_inst_2002_, v_inst_2003_, v_inst_2004_, v_inst_2005_, v_id_2006_, v_enableLog_boxed_2008_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_id_2017_, uint8_t v_enableLog_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_resolveGlobalName___redArg(v_inst_2011_, v_inst_2012_, v_inst_2013_, v_inst_2014_, v_inst_2015_, v_inst_2016_, v_id_2017_, v_enableLog_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_id_2027_, lean_object* v_enableLog_2028_){
_start:
{
uint8_t v_enableLog_boxed_2029_; lean_object* v_res_2030_; 
v_enableLog_boxed_2029_ = lean_unbox(v_enableLog_2028_);
v_res_2030_ = l_Lean_resolveGlobalName(v_m_2020_, v_inst_2021_, v_inst_2022_, v_inst_2023_, v_inst_2024_, v_inst_2025_, v_inst_2026_, v_id_2027_, v_enableLog_boxed_2029_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2031_, lean_object* v_nss_2032_, lean_object* v_____r_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_apply_2(v_toPure_2031_, lean_box(0), v_nss_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2037_, lean_object* v_____do__lift_2038_, lean_object* v_id_2039_, uint8_t v_allowEmpty_2040_, lean_object* v_toPure_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_toBind_2044_, lean_object* v_____do__lift_2045_){
_start:
{
lean_object* v_nss_2046_; 
lean_inc(v_id_2039_);
v_nss_2046_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2037_, v_____do__lift_2038_, v_____do__lift_2045_, v_id_2039_);
if (v_allowEmpty_2040_ == 0)
{
uint8_t v___x_2047_; 
v___x_2047_ = l_List_isEmpty___redArg(v_nss_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v_toBind_2044_);
lean_dec_ref(v_inst_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec(v_id_2039_);
v___x_2048_ = lean_apply_2(v_toPure_2041_, lean_box(0), v_nss_2046_);
return v___x_2048_;
}
else
{
lean_object* v___f_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2049_, 0, v_toPure_2041_);
lean_closure_set(v___f_2049_, 1, v_nss_2046_);
v___x_2050_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2051_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2039_, v___x_2047_);
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2054_ = lean_string_append(v___x_2052_, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
v___x_2056_ = l_Lean_MessageData_ofFormat(v___x_2055_);
v___x_2057_ = l_Lean_throwError___redArg(v_inst_2042_, v_inst_2043_, v___x_2056_);
v___x_2058_ = lean_apply_4(v_toBind_2044_, lean_box(0), lean_box(0), v___x_2057_, v___f_2049_);
return v___x_2058_;
}
}
else
{
lean_object* v___x_2059_; 
lean_dec(v_toBind_2044_);
lean_dec_ref(v_inst_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec(v_id_2039_);
v___x_2059_ = lean_apply_2(v_toPure_2041_, lean_box(0), v_nss_2046_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2060_, lean_object* v_____do__lift_2061_, lean_object* v_id_2062_, lean_object* v_allowEmpty_2063_, lean_object* v_toPure_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_toBind_2067_, lean_object* v_____do__lift_2068_){
_start:
{
uint8_t v_allowEmpty_boxed_2069_; lean_object* v_res_2070_; 
v_allowEmpty_boxed_2069_ = lean_unbox(v_allowEmpty_2063_);
v_res_2070_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2060_, v_____do__lift_2061_, v_id_2062_, v_allowEmpty_boxed_2069_, v_toPure_2064_, v_inst_2065_, v_inst_2066_, v_toBind_2067_, v_____do__lift_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2071_, lean_object* v_id_2072_, uint8_t v_allowEmpty_2073_, lean_object* v_toPure_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_toBind_2077_, lean_object* v_getOpenDecls_2078_, lean_object* v_____do__lift_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(v_allowEmpty_2073_);
lean_inc(v_toBind_2077_);
v___f_2081_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2081_, 0, v_____do__lift_2071_);
lean_closure_set(v___f_2081_, 1, v_____do__lift_2079_);
lean_closure_set(v___f_2081_, 2, v_id_2072_);
lean_closure_set(v___f_2081_, 3, v___x_2080_);
lean_closure_set(v___f_2081_, 4, v_toPure_2074_);
lean_closure_set(v___f_2081_, 5, v_inst_2075_);
lean_closure_set(v___f_2081_, 6, v_inst_2076_);
lean_closure_set(v___f_2081_, 7, v_toBind_2077_);
v___x_2082_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v_getOpenDecls_2078_, v___f_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2083_, lean_object* v_id_2084_, lean_object* v_allowEmpty_2085_, lean_object* v_toPure_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_toBind_2089_, lean_object* v_getOpenDecls_2090_, lean_object* v_____do__lift_2091_){
_start:
{
uint8_t v_allowEmpty_boxed_2092_; lean_object* v_res_2093_; 
v_allowEmpty_boxed_2092_ = lean_unbox(v_allowEmpty_2085_);
v_res_2093_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2083_, v_id_2084_, v_allowEmpty_boxed_2092_, v_toPure_2086_, v_inst_2087_, v_inst_2088_, v_toBind_2089_, v_getOpenDecls_2090_, v_____do__lift_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2094_, lean_object* v_id_2095_, uint8_t v_allowEmpty_2096_, lean_object* v_toPure_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_toBind_2100_, lean_object* v_____do__lift_2101_){
_start:
{
lean_object* v_getCurrNamespace_2102_; lean_object* v_getOpenDecls_2103_; lean_object* v___x_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; 
v_getCurrNamespace_2102_ = lean_ctor_get(v_inst_2094_, 0);
lean_inc(v_getCurrNamespace_2102_);
v_getOpenDecls_2103_ = lean_ctor_get(v_inst_2094_, 1);
lean_inc(v_getOpenDecls_2103_);
lean_dec_ref(v_inst_2094_);
v___x_2104_ = lean_box(v_allowEmpty_2096_);
lean_inc(v_toBind_2100_);
v___f_2105_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2105_, 0, v_____do__lift_2101_);
lean_closure_set(v___f_2105_, 1, v_id_2095_);
lean_closure_set(v___f_2105_, 2, v___x_2104_);
lean_closure_set(v___f_2105_, 3, v_toPure_2097_);
lean_closure_set(v___f_2105_, 4, v_inst_2098_);
lean_closure_set(v___f_2105_, 5, v_inst_2099_);
lean_closure_set(v___f_2105_, 6, v_toBind_2100_);
lean_closure_set(v___f_2105_, 7, v_getOpenDecls_2103_);
v___x_2106_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v_getCurrNamespace_2102_, v___f_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2107_, lean_object* v_id_2108_, lean_object* v_allowEmpty_2109_, lean_object* v_toPure_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_toBind_2113_, lean_object* v_____do__lift_2114_){
_start:
{
uint8_t v_allowEmpty_boxed_2115_; lean_object* v_res_2116_; 
v_allowEmpty_boxed_2115_ = lean_unbox(v_allowEmpty_2109_);
v_res_2116_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2107_, v_id_2108_, v_allowEmpty_boxed_2115_, v_toPure_2110_, v_inst_2111_, v_inst_2112_, v_toBind_2113_, v_____do__lift_2114_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_id_2121_, uint8_t v_allowEmpty_2122_){
_start:
{
lean_object* v_toApplicative_2123_; lean_object* v_toBind_2124_; lean_object* v_getEnv_2125_; lean_object* v_toPure_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; 
v_toApplicative_2123_ = lean_ctor_get(v_inst_2117_, 0);
v_toBind_2124_ = lean_ctor_get(v_inst_2117_, 1);
lean_inc_n(v_toBind_2124_, 2);
v_getEnv_2125_ = lean_ctor_get(v_inst_2119_, 0);
lean_inc(v_getEnv_2125_);
lean_dec_ref(v_inst_2119_);
v_toPure_2126_ = lean_ctor_get(v_toApplicative_2123_, 1);
lean_inc(v_toPure_2126_);
v___x_2127_ = lean_box(v_allowEmpty_2122_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2128_, 0, v_inst_2118_);
lean_closure_set(v___f_2128_, 1, v_id_2121_);
lean_closure_set(v___f_2128_, 2, v___x_2127_);
lean_closure_set(v___f_2128_, 3, v_toPure_2126_);
lean_closure_set(v___f_2128_, 4, v_inst_2117_);
lean_closure_set(v___f_2128_, 5, v_inst_2120_);
lean_closure_set(v___f_2128_, 6, v_toBind_2124_);
v___x_2129_ = lean_apply_4(v_toBind_2124_, lean_box(0), lean_box(0), v_getEnv_2125_, v___f_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_id_2134_, lean_object* v_allowEmpty_2135_){
_start:
{
uint8_t v_allowEmpty_boxed_2136_; lean_object* v_res_2137_; 
v_allowEmpty_boxed_2136_ = lean_unbox(v_allowEmpty_2135_);
v_res_2137_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2130_, v_inst_2131_, v_inst_2132_, v_inst_2133_, v_id_2134_, v_allowEmpty_boxed_2136_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_id_2143_, uint8_t v_allowEmpty_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_id_2143_, v_allowEmpty_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_id_2151_, lean_object* v_allowEmpty_2152_){
_start:
{
uint8_t v_allowEmpty_boxed_2153_; lean_object* v_res_2154_; 
v_allowEmpty_boxed_2153_ = lean_unbox(v_allowEmpty_2152_);
v_res_2154_ = l_Lean_resolveNamespaceCore(v_m_2146_, v_inst_2147_, v_inst_2148_, v_inst_2149_, v_inst_2150_, v_id_2151_, v_allowEmpty_boxed_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2155_){
_start:
{
if (lean_obj_tag(v_x_2155_) == 0)
{
lean_object* v_ns_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
v_ns_2156_ = lean_ctor_get(v_x_2155_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v_x_2155_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_ns_2156_);
lean_dec(v_x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 1);
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_ns_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v___x_2164_; 
lean_dec_ref(v_x_2155_);
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2165_, lean_object* v_withRef_2166_, lean_object* v___x_2167_, lean_object* v_oldRef_2168_){
_start:
{
lean_object* v_ref_2169_; lean_object* v___x_2170_; 
v_ref_2169_ = l_Lean_replaceRef(v_x_2165_, v_oldRef_2168_);
v___x_2170_ = lean_apply_3(v_withRef_2166_, lean_box(0), v_ref_2169_, v___x_2167_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2171_, lean_object* v_withRef_2172_, lean_object* v___x_2173_, lean_object* v_oldRef_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2171_, v_withRef_2172_, v___x_2173_, v_oldRef_2174_);
lean_dec(v_oldRef_2174_);
lean_dec(v_x_2171_);
return v_res_2175_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2183_ = l_Lean_MessageData_ofFormat(v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_x_2188_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 3)
{
lean_object* v_toApplicative_2189_; lean_object* v_toBind_2190_; lean_object* v_toPure_2191_; lean_object* v_toMonadRef_2192_; lean_object* v_val_2193_; lean_object* v_preresolved_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v_pre_2197_; uint8_t v___x_2198_; 
v_toApplicative_2189_ = lean_ctor_get(v_inst_2184_, 0);
v_toBind_2190_ = lean_ctor_get(v_inst_2184_, 1);
lean_inc(v_toBind_2190_);
v_toPure_2191_ = lean_ctor_get(v_toApplicative_2189_, 1);
v_toMonadRef_2192_ = lean_ctor_get(v_inst_2187_, 1);
v_val_2193_ = lean_ctor_get(v_x_2188_, 2);
v_preresolved_2194_ = lean_ctor_get(v_x_2188_, 3);
v___f_2195_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2196_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2194_);
v_pre_2197_ = l_List_filterMapTR_go___redArg(v___f_2195_, v_preresolved_2194_, v___x_2196_);
v___x_2198_ = l_List_isEmpty___redArg(v_pre_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_inc(v_toPure_2191_);
lean_dec(v_toBind_2190_);
lean_dec_ref_known(v_x_2188_, 4);
lean_dec_ref(v_inst_2187_);
lean_dec_ref(v_inst_2186_);
lean_dec_ref(v_inst_2185_);
lean_dec_ref(v_inst_2184_);
v___x_2199_ = lean_apply_2(v_toPure_2191_, lean_box(0), v_pre_2197_);
return v___x_2199_;
}
else
{
lean_object* v_getRef_2200_; lean_object* v_withRef_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
lean_dec(v_pre_2197_);
v_getRef_2200_ = lean_ctor_get(v_toMonadRef_2192_, 0);
lean_inc(v_getRef_2200_);
v_withRef_2201_ = lean_ctor_get(v_toMonadRef_2192_, 1);
lean_inc(v_withRef_2201_);
v___x_2202_ = 0;
lean_inc(v_val_2193_);
v___x_2203_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2184_, v_inst_2185_, v_inst_2186_, v_inst_2187_, v_val_2193_, v___x_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2204_, 0, v_x_2188_);
lean_closure_set(v___f_2204_, 1, v_withRef_2201_);
lean_closure_set(v___f_2204_, 2, v___x_2203_);
v___x_2205_ = lean_apply_4(v_toBind_2190_, lean_box(0), lean_box(0), v_getRef_2200_, v___f_2204_);
return v___x_2205_;
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v_inst_2186_);
lean_dec_ref(v_inst_2185_);
v___x_2206_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2207_ = l_Lean_throwErrorAt___redArg(v_inst_2184_, v_inst_2187_, v_x_2188_, v___x_2206_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2208_, lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_resolveNamespace___redArg(v_inst_2209_, v_inst_2210_, v_inst_2211_, v_inst_2212_, v_x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2217_, lean_object* v___f_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_toPure_2221_, lean_object* v_____do__lift_2222_){
_start:
{
if (lean_obj_tag(v_____do__lift_2222_) == 1)
{
lean_object* v_tail_2238_; 
v_tail_2238_ = lean_ctor_get(v_____do__lift_2222_, 1);
if (lean_obj_tag(v_tail_2238_) == 0)
{
lean_object* v_head_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_inst_2220_);
lean_dec_ref(v_inst_2219_);
lean_dec_ref(v___f_2218_);
v_head_2239_ = lean_ctor_get(v_____do__lift_2222_, 0);
lean_inc(v_head_2239_);
lean_dec_ref_known(v_____do__lift_2222_, 2);
v___x_2240_ = lean_apply_2(v_toPure_2221_, lean_box(0), v_head_2239_);
return v___x_2240_;
}
else
{
lean_dec(v_toPure_2221_);
goto v___jp_2223_;
}
}
else
{
lean_dec(v_toPure_2221_);
goto v___jp_2223_;
}
v___jp_2223_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2224_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2225_ = l_Lean_TSyntax_getId(v_id_2217_);
v___x_2226_ = 1;
v___x_2227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2225_, v___x_2226_);
v___x_2228_ = lean_string_append(v___x_2224_, v___x_2227_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2230_ = lean_string_append(v___x_2228_, v___x_2229_);
v___x_2231_ = l_List_toString___redArg(v___f_2218_, v_____do__lift_2222_);
v___x_2232_ = lean_string_append(v___x_2230_, v___x_2231_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2234_ = lean_string_append(v___x_2232_, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
v___x_2236_ = l_Lean_MessageData_ofFormat(v___x_2235_);
v___x_2237_ = l_Lean_throwError___redArg(v_inst_2219_, v_inst_2220_, v___x_2236_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2241_, lean_object* v___f_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_toPure_2245_, lean_object* v_____do__lift_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2241_, v___f_2242_, v_inst_2243_, v_inst_2244_, v_toPure_2245_, v_____do__lift_2246_);
lean_dec(v_id_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_id_2253_){
_start:
{
lean_object* v_toApplicative_2254_; lean_object* v_toBind_2255_; lean_object* v_toPure_2256_; lean_object* v___f_2257_; lean_object* v___x_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; 
v_toApplicative_2254_ = lean_ctor_get(v_inst_2249_, 0);
v_toBind_2255_ = lean_ctor_get(v_inst_2249_, 1);
lean_inc(v_toBind_2255_);
v_toPure_2256_ = lean_ctor_get(v_toApplicative_2254_, 1);
lean_inc(v_toPure_2256_);
v___f_2257_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2253_);
lean_inc_ref(v_inst_2252_);
lean_inc_ref(v_inst_2249_);
v___x_2258_ = l_Lean_resolveNamespace___redArg(v_inst_2249_, v_inst_2250_, v_inst_2251_, v_inst_2252_, v_id_2253_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2259_, 0, v_id_2253_);
lean_closure_set(v___f_2259_, 1, v___f_2257_);
lean_closure_set(v___f_2259_, 2, v_inst_2249_);
lean_closure_set(v___f_2259_, 3, v_inst_2252_);
lean_closure_set(v___f_2259_, 4, v_toPure_2256_);
v___x_2260_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v___x_2258_, v___f_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_id_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2262_, v_inst_2263_, v_inst_2264_, v_inst_2265_, v_id_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2268_){
_start:
{
lean_object* v_snd_2269_; uint8_t v___x_2270_; 
v_snd_2269_ = lean_ctor_get(v_x_2268_, 1);
v___x_2270_ = l_List_isEmpty___redArg(v_snd_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2271_){
_start:
{
uint8_t v_res_2272_; lean_object* v_r_2273_; 
v_res_2272_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2271_);
lean_dec_ref(v_x_2271_);
v_r_2273_ = lean_box(v_res_2272_);
return v_r_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2274_){
_start:
{
lean_object* v_fst_2275_; 
v_fst_2275_ = lean_ctor_get(v_x_2274_, 0);
lean_inc(v_fst_2275_);
return v_fst_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2276_);
lean_dec_ref(v_x_2276_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2278_, lean_object* v_cs_2279_, lean_object* v_toPure_2280_, lean_object* v_____r_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = l_List_mapTR_loop___redArg(v___f_2278_, v_cs_2279_, v___x_2282_);
v___x_2284_ = lean_apply_2(v_toPure_2280_, lean_box(0), v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2285_, lean_object* v_____r_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_apply_1(v___f_2285_, v_____r_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_n_2291_, lean_object* v_toBind_2292_, lean_object* v___f_2293_, lean_object* v_____do__lift_2294_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2288_, v_inst_2289_, v_inst_2290_, v_____do__lift_2294_, v_n_2291_);
v___x_2296_ = lean_apply_4(v_toBind_2292_, lean_box(0), lean_box(0), v___x_2295_, v___f_2293_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_n_2302_, lean_object* v_cs_2303_){
_start:
{
lean_object* v_toApplicative_2304_; lean_object* v_toBind_2305_; lean_object* v_toPure_2306_; lean_object* v_toMonadRef_2307_; lean_object* v___f_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; lean_object* v_cs_2311_; lean_object* v___f_2312_; uint8_t v___x_2313_; 
v_toApplicative_2304_ = lean_ctor_get(v_inst_2299_, 0);
v_toBind_2305_ = lean_ctor_get(v_inst_2299_, 1);
lean_inc(v_toBind_2305_);
v_toPure_2306_ = lean_ctor_get(v_toApplicative_2304_, 1);
v_toMonadRef_2307_ = lean_ctor_get(v_inst_2301_, 1);
v___f_2308_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2309_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2310_ = lean_box(0);
v_cs_2311_ = l_List_filterTR_loop___redArg(v___f_2308_, v_cs_2303_, v___x_2310_);
lean_inc(v_toPure_2306_);
lean_inc(v_cs_2311_);
v___f_2312_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2312_, 0, v___f_2309_);
lean_closure_set(v___f_2312_, 1, v_cs_2311_);
lean_closure_set(v___f_2312_, 2, v_toPure_2306_);
v___x_2313_ = l_List_isEmpty___redArg(v_cs_2311_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_inc(v_toPure_2306_);
lean_dec_ref(v___f_2312_);
lean_dec(v_toBind_2305_);
lean_dec(v_n_2302_);
lean_dec_ref(v_inst_2301_);
lean_dec_ref(v_inst_2300_);
lean_dec_ref(v_inst_2299_);
v___x_2314_ = lean_box(0);
v___x_2315_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2309_, v_cs_2311_, v_toPure_2306_, v___x_2314_);
return v___x_2315_;
}
else
{
lean_object* v_getRef_2316_; lean_object* v___f_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; 
lean_dec(v_cs_2311_);
v_getRef_2316_ = lean_ctor_get(v_toMonadRef_2307_, 0);
lean_inc(v_getRef_2316_);
v___f_2317_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2317_, 0, v___f_2312_);
lean_inc(v_toBind_2305_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2318_, 0, v_inst_2299_);
lean_closure_set(v___f_2318_, 1, v_inst_2300_);
lean_closure_set(v___f_2318_, 2, v_inst_2301_);
lean_closure_set(v___f_2318_, 3, v_n_2302_);
lean_closure_set(v___f_2318_, 4, v_toBind_2305_);
lean_closure_set(v___f_2318_, 5, v___f_2317_);
v___x_2319_ = lean_apply_4(v_toBind_2305_, lean_box(0), lean_box(0), v_getRef_2316_, v___f_2318_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_n_2324_, lean_object* v_cs_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_filterFieldList___redArg(v_inst_2321_, v_inst_2322_, v_inst_2323_, v_n_2324_, v_cs_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_n_2330_, lean_object* v_cs_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_filterFieldList___redArg(v_inst_2327_, v_inst_2328_, v_inst_2329_, v_n_2330_, v_cs_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_n_2340_){
_start:
{
lean_object* v_toBind_2341_; lean_object* v___f_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_toBind_2341_ = lean_ctor_get(v_inst_2333_, 1);
lean_inc(v_toBind_2341_);
lean_inc(v_n_2340_);
lean_inc_ref(v_inst_2335_);
lean_inc_ref(v_inst_2333_);
v___f_2342_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2342_, 0, v_inst_2333_);
lean_closure_set(v___f_2342_, 1, v_inst_2335_);
lean_closure_set(v___f_2342_, 2, v_inst_2339_);
lean_closure_set(v___f_2342_, 3, v_n_2340_);
v___x_2343_ = 1;
v___x_2344_ = l_Lean_resolveGlobalName___redArg(v_inst_2333_, v_inst_2334_, v_inst_2335_, v_inst_2336_, v_inst_2337_, v_inst_2338_, v_n_2340_, v___x_2343_);
v___x_2345_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v___x_2344_, v___f_2342_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_n_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2347_, v_inst_2348_, v_inst_2349_, v_inst_2350_, v_inst_2351_, v_inst_2352_, v_inst_2353_, v_n_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = l_Lean_mkConst(v_declName_2356_, v___x_2357_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2362_ = l_Lean_stringToMessageData(v___x_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2365_ = l_Lean_stringToMessageData(v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_n_2369_, lean_object* v_cs_2370_){
_start:
{
lean_object* v_toApplicative_2371_; lean_object* v_toPure_2372_; lean_object* v___f_2373_; 
v_toApplicative_2371_ = lean_ctor_get(v_inst_2367_, 0);
v_toPure_2372_ = lean_ctor_get(v_toApplicative_2371_, 1);
v___f_2373_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2370_) == 1)
{
lean_object* v_tail_2387_; 
v_tail_2387_ = lean_ctor_get(v_cs_2370_, 1);
if (lean_obj_tag(v_tail_2387_) == 0)
{
lean_object* v_head_2388_; lean_object* v___x_2389_; 
lean_inc(v_toPure_2372_);
lean_dec(v_n_2369_);
lean_dec_ref(v_inst_2368_);
lean_dec_ref(v_inst_2367_);
v_head_2388_ = lean_ctor_get(v_cs_2370_, 0);
lean_inc(v_head_2388_);
lean_dec_ref_known(v_cs_2370_, 2);
v___x_2389_ = lean_apply_2(v_toPure_2372_, lean_box(0), v_head_2388_);
return v___x_2389_;
}
else
{
goto v___jp_2374_;
}
}
else
{
goto v___jp_2374_;
}
v___jp_2374_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2375_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2376_ = l_Lean_MessageData_ofName(v_n_2369_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_box(0);
v___x_2381_ = l_List_mapTR_loop___redArg(v___f_2373_, v_cs_2370_, v___x_2380_);
v___x_2382_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2383_ = l_List_mapTR_loop___redArg(v___x_2382_, v___x_2381_, v___x_2380_);
v___x_2384_ = l_Lean_MessageData_ofList(v___x_2383_);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2379_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = l_Lean_throwError___redArg(v_inst_2367_, v_inst_2368_, v___x_2385_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_n_2393_, lean_object* v_cs_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_ensureNoOverload___redArg(v_inst_2391_, v_inst_2392_, v_n_2393_, v_cs_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_n_2398_, lean_object* v_____do__lift_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_ensureNoOverload___redArg(v_inst_2396_, v_inst_2397_, v_n_2398_, v_____do__lift_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_inst_2404_, lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_n_2408_){
_start:
{
lean_object* v_toBind_2409_; lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_toBind_2409_ = lean_ctor_get(v_inst_2401_, 1);
lean_inc(v_toBind_2409_);
lean_inc(v_n_2408_);
lean_inc_ref(v_inst_2407_);
lean_inc_ref(v_inst_2401_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2410_, 0, v_inst_2401_);
lean_closure_set(v___f_2410_, 1, v_inst_2407_);
lean_closure_set(v___f_2410_, 2, v_n_2408_);
v___x_2411_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2401_, v_inst_2402_, v_inst_2403_, v_inst_2404_, v_inst_2405_, v_inst_2406_, v_inst_2407_, v_n_2408_);
v___x_2412_ = lean_apply_4(v_toBind_2409_, lean_box(0), lean_box(0), v___x_2411_, v___f_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_n_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_inst_2417_, v_inst_2418_, v_inst_2419_, v_inst_2420_, v_n_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2423_){
_start:
{
if (lean_obj_tag(v_x_2423_) == 1)
{
lean_object* v_fields_2424_; 
v_fields_2424_ = lean_ctor_get(v_x_2423_, 1);
if (lean_obj_tag(v_fields_2424_) == 0)
{
lean_object* v_n_2425_; lean_object* v___x_2426_; 
v_n_2425_ = lean_ctor_get(v_x_2423_, 0);
lean_inc(v_n_2425_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_n_2425_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_box(0);
return v___x_2427_;
}
}
else
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_box(0);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2429_);
lean_dec_ref(v_x_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2431_, lean_object* v_withRef_2432_, lean_object* v___x_2433_, lean_object* v_oldRef_2434_){
_start:
{
lean_object* v_ref_2435_; lean_object* v___x_2436_; 
v_ref_2435_ = l_Lean_replaceRef(v_stx_2431_, v_oldRef_2434_);
v___x_2436_ = lean_apply_3(v_withRef_2432_, lean_box(0), v_ref_2435_, v___x_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2437_, lean_object* v_withRef_2438_, lean_object* v___x_2439_, lean_object* v_oldRef_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2437_, v_withRef_2438_, v___x_2439_, v_oldRef_2440_);
lean_dec(v_oldRef_2440_);
lean_dec(v_stx_2437_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_stx_2445_, lean_object* v_k_2446_){
_start:
{
if (lean_obj_tag(v_stx_2445_) == 3)
{
lean_object* v_toApplicative_2447_; lean_object* v_toBind_2448_; lean_object* v_toPure_2449_; lean_object* v_toMonadRef_2450_; lean_object* v_val_2451_; lean_object* v_preresolved_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; lean_object* v_pre_2455_; uint8_t v___x_2456_; 
v_toApplicative_2447_ = lean_ctor_get(v_inst_2443_, 0);
lean_inc_ref(v_toApplicative_2447_);
v_toBind_2448_ = lean_ctor_get(v_inst_2443_, 1);
lean_inc(v_toBind_2448_);
lean_dec_ref(v_inst_2443_);
v_toPure_2449_ = lean_ctor_get(v_toApplicative_2447_, 1);
lean_inc(v_toPure_2449_);
lean_dec_ref(v_toApplicative_2447_);
v_toMonadRef_2450_ = lean_ctor_get(v_inst_2444_, 1);
lean_inc_ref(v_toMonadRef_2450_);
lean_dec_ref(v_inst_2444_);
v_val_2451_ = lean_ctor_get(v_stx_2445_, 2);
v_preresolved_2452_ = lean_ctor_get(v_stx_2445_, 3);
v___f_2453_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2454_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2452_);
v_pre_2455_ = l_List_filterMapTR_go___redArg(v___f_2453_, v_preresolved_2452_, v___x_2454_);
v___x_2456_ = l_List_isEmpty___redArg(v_pre_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v_toMonadRef_2450_);
lean_dec_ref_known(v_stx_2445_, 4);
lean_dec(v_toBind_2448_);
lean_dec(v_k_2446_);
v___x_2457_ = lean_apply_2(v_toPure_2449_, lean_box(0), v_pre_2455_);
return v___x_2457_;
}
else
{
lean_object* v_getRef_2458_; lean_object* v_withRef_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; 
lean_dec(v_pre_2455_);
lean_dec(v_toPure_2449_);
v_getRef_2458_ = lean_ctor_get(v_toMonadRef_2450_, 0);
lean_inc(v_getRef_2458_);
v_withRef_2459_ = lean_ctor_get(v_toMonadRef_2450_, 1);
lean_inc(v_withRef_2459_);
lean_dec_ref(v_toMonadRef_2450_);
lean_inc(v_val_2451_);
v___x_2460_ = lean_apply_1(v_k_2446_, v_val_2451_);
v___f_2461_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2461_, 0, v_stx_2445_);
lean_closure_set(v___f_2461_, 1, v_withRef_2459_);
lean_closure_set(v___f_2461_, 2, v___x_2460_);
v___x_2462_ = lean_apply_4(v_toBind_2448_, lean_box(0), lean_box(0), v_getRef_2458_, v___f_2461_);
return v___x_2462_;
}
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec(v_k_2446_);
v___x_2463_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2464_ = l_Lean_throwErrorAt___redArg(v_inst_2443_, v_inst_2444_, v_stx_2445_, v___x_2463_);
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_stx_2468_, lean_object* v_k_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2466_, v_inst_2467_, v_stx_2468_, v_k_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_stx_2478_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_inc_ref(v_inst_2477_);
lean_inc_ref(v_inst_2471_);
v___x_2479_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2479_, 0, lean_box(0));
lean_closure_set(v___x_2479_, 1, v_inst_2471_);
lean_closure_set(v___x_2479_, 2, v_inst_2472_);
lean_closure_set(v___x_2479_, 3, v_inst_2473_);
lean_closure_set(v___x_2479_, 4, v_inst_2474_);
lean_closure_set(v___x_2479_, 5, v_inst_2475_);
lean_closure_set(v___x_2479_, 6, v_inst_2476_);
lean_closure_set(v___x_2479_, 7, v_inst_2477_);
v___x_2480_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2471_, v_inst_2477_, v_stx_2478_, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_stx_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_resolveGlobalConst___redArg(v_inst_2482_, v_inst_2483_, v_inst_2484_, v_inst_2485_, v_inst_2486_, v_inst_2487_, v_inst_2488_, v_stx_2489_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2492_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2493_ = lean_unsigned_to_nat(11u);
v___x_2494_ = lean_unsigned_to_nat(429u);
v___x_2495_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2496_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2497_ = l_mkPanicMessageWithDecl(v___x_2496_, v___x_2495_, v___x_2494_, v___x_2493_, v___x_2492_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_id_2503_, lean_object* v_cs_2504_){
_start:
{
if (lean_obj_tag(v_cs_2504_) == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec(v_id_2503_);
lean_dec_ref(v_inst_2502_);
v___x_2505_ = lean_box(0);
v___x_2506_ = l_instInhabitedOfMonad___redArg(v_inst_2501_, v___x_2505_);
v___x_2507_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2508_ = l_panic___redArg(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
return v___x_2508_;
}
else
{
lean_object* v_tail_2509_; 
v_tail_2509_ = lean_ctor_get(v_cs_2504_, 1);
if (lean_obj_tag(v_tail_2509_) == 0)
{
lean_object* v_toApplicative_2510_; lean_object* v_toPure_2511_; lean_object* v_head_2512_; lean_object* v___x_2513_; 
v_toApplicative_2510_ = lean_ctor_get(v_inst_2501_, 0);
lean_inc_ref(v_toApplicative_2510_);
lean_dec(v_id_2503_);
lean_dec_ref(v_inst_2502_);
lean_dec_ref(v_inst_2501_);
v_toPure_2511_ = lean_ctor_get(v_toApplicative_2510_, 1);
lean_inc(v_toPure_2511_);
lean_dec_ref(v_toApplicative_2510_);
v_head_2512_ = lean_ctor_get(v_cs_2504_, 0);
lean_inc(v_head_2512_);
lean_dec_ref_known(v_cs_2504_, 2);
v___x_2513_ = lean_apply_2(v_toPure_2511_, lean_box(0), v_head_2512_);
return v___x_2513_;
}
else
{
lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___f_2514_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2515_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2516_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2517_ = lean_box(0);
v___x_2518_ = 0;
lean_inc(v_id_2503_);
v___x_2519_ = l_Lean_Syntax_formatStx(v_id_2503_, v___x_2517_, v___x_2518_);
v___x_2520_ = l_Std_Format_defWidth;
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = l_Std_Format_pretty(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2521_);
v___x_2523_ = lean_string_append(v___x_2516_, v___x_2522_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2525_ = lean_string_append(v___x_2523_, v___x_2524_);
v___x_2526_ = lean_box(0);
v___x_2527_ = l_List_mapTR_loop___redArg(v___f_2514_, v_cs_2504_, v___x_2526_);
v___x_2528_ = l_List_toString___redArg(v___x_2515_, v___x_2527_);
v___x_2529_ = lean_string_append(v___x_2525_, v___x_2528_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
v___x_2531_ = l_Lean_MessageData_ofFormat(v___x_2530_);
v___x_2532_ = l_Lean_throwErrorAt___redArg(v_inst_2501_, v_inst_2502_, v_id_2503_, v___x_2531_);
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_id_2536_, lean_object* v_cs_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2534_, v_inst_2535_, v_id_2536_, v_cs_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_id_2541_, lean_object* v_____do__lift_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2539_, v_inst_2540_, v_id_2541_, v_____do__lift_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_id_2551_){
_start:
{
lean_object* v_toBind_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_toBind_2552_ = lean_ctor_get(v_inst_2544_, 1);
lean_inc(v_toBind_2552_);
lean_inc(v_id_2551_);
lean_inc_ref(v_inst_2550_);
lean_inc_ref(v_inst_2544_);
v___f_2553_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2553_, 0, v_inst_2544_);
lean_closure_set(v___f_2553_, 1, v_inst_2550_);
lean_closure_set(v___f_2553_, 2, v_id_2551_);
v___x_2554_ = l_Lean_resolveGlobalConst___redArg(v_inst_2544_, v_inst_2545_, v_inst_2546_, v_inst_2547_, v_inst_2548_, v_inst_2549_, v_inst_2550_, v_id_2551_);
v___x_2555_ = lean_apply_4(v_toBind_2552_, lean_box(0), lean_box(0), v___x_2554_, v___f_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_id_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2557_, v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_inst_2562_, v_inst_2563_, v_id_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2566_, lean_object* v___f_2567_, uint8_t v_globalDeclFoundNext_2568_, uint8_t v_globalDeclFound_2569_, lean_object* v_r_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v_r_2572_; uint8_t v___x_2573_; 
v___x_2571_ = lean_box(0);
v_r_2572_ = l_List_filterTR_loop___redArg(v___f_2566_, v_r_2570_, v___x_2571_);
v___x_2573_ = l_List_isEmpty___redArg(v_r_2572_);
lean_dec(v_r_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_box(0);
v___x_2575_ = lean_box(v_globalDeclFoundNext_2568_);
v___x_2576_ = lean_apply_2(v___f_2567_, v___x_2574_, v___x_2575_);
return v___x_2576_;
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_box(v_globalDeclFound_2569_);
v___x_2579_ = lean_apply_2(v___f_2567_, v___x_2577_, v___x_2578_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2580_, lean_object* v___f_2581_, lean_object* v_globalDeclFoundNext_2582_, lean_object* v_globalDeclFound_2583_, lean_object* v_r_2584_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2585_; uint8_t v_globalDeclFound_boxed_2586_; lean_object* v_res_2587_; 
v_globalDeclFoundNext_boxed_2585_ = lean_unbox(v_globalDeclFoundNext_2582_);
v_globalDeclFound_boxed_2586_ = lean_unbox(v_globalDeclFound_2583_);
v_res_2587_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2580_, v___f_2581_, v_globalDeclFoundNext_boxed_2585_, v_globalDeclFound_boxed_2586_, v_r_2584_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2588_, lean_object* v_projs_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_view_2596_, lean_object* v_findLocalDecl_x3f_2597_, lean_object* v_pre_2598_, lean_object* v_____r_2599_, lean_object* v_globalDeclFoundNext_2600_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2601_; lean_object* v_res_2602_; 
v_globalDeclFoundNext_boxed_2601_ = lean_unbox(v_globalDeclFoundNext_2600_);
v_res_2602_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2588_, v_projs_2589_, v_inst_2590_, v_inst_2591_, v_inst_2592_, v_inst_2593_, v_inst_2594_, v_inst_2595_, v_view_2596_, v_findLocalDecl_x3f_2597_, v_pre_2598_, v_____r_2599_, v_globalDeclFoundNext_boxed_2601_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_view_2609_, lean_object* v_findLocalDecl_x3f_2610_, lean_object* v_n_2611_, lean_object* v_projs_2612_, uint8_t v_globalDeclFound_2613_){
_start:
{
lean_object* v_toApplicative_2614_; lean_object* v_imported_2615_; lean_object* v_ctx_2616_; lean_object* v_scopes_2617_; lean_object* v_toBind_2618_; lean_object* v_toPure_2619_; lean_object* v___f_2620_; lean_object* v_givenNameView_2621_; uint8_t v___y_2623_; 
v_toApplicative_2614_ = lean_ctor_get(v_inst_2603_, 0);
v_imported_2615_ = lean_ctor_get(v_view_2609_, 1);
v_ctx_2616_ = lean_ctor_get(v_view_2609_, 2);
v_scopes_2617_ = lean_ctor_get(v_view_2609_, 3);
v_toBind_2618_ = lean_ctor_get(v_inst_2603_, 1);
v_toPure_2619_ = lean_ctor_get(v_toApplicative_2614_, 1);
v___f_2620_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2617_);
lean_inc(v_ctx_2616_);
lean_inc(v_imported_2615_);
lean_inc(v_n_2611_);
v_givenNameView_2621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2621_, 0, v_n_2611_);
lean_ctor_set(v_givenNameView_2621_, 1, v_imported_2615_);
lean_ctor_set(v_givenNameView_2621_, 2, v_ctx_2616_);
lean_ctor_set(v_givenNameView_2621_, 3, v_scopes_2617_);
if (v_globalDeclFound_2613_ == 0)
{
v___y_2623_ = v_globalDeclFound_2613_;
goto v___jp_2622_;
}
else
{
uint8_t v___x_2659_; 
v___x_2659_ = l_List_isEmpty___redArg(v_projs_2612_);
if (v___x_2659_ == 0)
{
v___y_2623_ = v_globalDeclFound_2613_;
goto v___jp_2622_;
}
else
{
uint8_t v___x_2660_; 
v___x_2660_ = 0;
v___y_2623_ = v___x_2660_;
goto v___jp_2622_;
}
}
v___jp_2622_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(v___y_2623_);
lean_inc_ref(v_findLocalDecl_x3f_2610_);
lean_inc_ref(v_givenNameView_2621_);
v___x_2625_ = lean_apply_2(v_findLocalDecl_x3f_2610_, v_givenNameView_2621_, v___x_2624_);
if (lean_obj_tag(v___x_2625_) == 0)
{
if (lean_obj_tag(v_n_2611_) == 1)
{
lean_object* v_pre_2626_; lean_object* v_str_2627_; lean_object* v___f_2628_; 
v_pre_2626_ = lean_ctor_get(v_n_2611_, 0);
lean_inc_n(v_pre_2626_, 2);
v_str_2627_ = lean_ctor_get(v_n_2611_, 1);
lean_inc_ref_n(v_str_2627_, 2);
lean_dec_ref_known(v_n_2611_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2610_);
lean_inc_ref(v_view_2609_);
lean_inc(v_inst_2608_);
lean_inc_ref(v_inst_2607_);
lean_inc(v_inst_2606_);
lean_inc_ref(v_inst_2605_);
lean_inc_ref(v_inst_2604_);
lean_inc_ref(v_inst_2603_);
lean_inc(v_projs_2612_);
v___f_2628_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2628_, 0, v_str_2627_);
lean_closure_set(v___f_2628_, 1, v_projs_2612_);
lean_closure_set(v___f_2628_, 2, v_inst_2603_);
lean_closure_set(v___f_2628_, 3, v_inst_2604_);
lean_closure_set(v___f_2628_, 4, v_inst_2605_);
lean_closure_set(v___f_2628_, 5, v_inst_2606_);
lean_closure_set(v___f_2628_, 6, v_inst_2607_);
lean_closure_set(v___f_2628_, 7, v_inst_2608_);
lean_closure_set(v___f_2628_, 8, v_view_2609_);
lean_closure_set(v___f_2628_, 9, v_findLocalDecl_x3f_2610_);
lean_closure_set(v___f_2628_, 10, v_pre_2626_);
if (v_globalDeclFound_2613_ == 0)
{
uint8_t v_globalDeclFoundNext_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc(v_toBind_2618_);
lean_dec_ref(v_str_2627_);
lean_dec(v_pre_2626_);
lean_dec(v_projs_2612_);
lean_dec_ref(v_findLocalDecl_x3f_2610_);
lean_dec_ref(v_view_2609_);
v_globalDeclFoundNext_2629_ = 1;
v___x_2630_ = lean_box(v_globalDeclFoundNext_2629_);
v___x_2631_ = lean_box(v_globalDeclFound_2613_);
v___f_2632_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2632_, 0, v___f_2620_);
lean_closure_set(v___f_2632_, 1, v___f_2628_);
lean_closure_set(v___f_2632_, 2, v___x_2630_);
lean_closure_set(v___f_2632_, 3, v___x_2631_);
v___x_2633_ = l_Lean_MacroScopesView_review(v_givenNameView_2621_);
v___x_2634_ = l_Lean_resolveGlobalName___redArg(v_inst_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v_inst_2608_, v___x_2633_, v_globalDeclFound_2613_);
v___x_2635_ = lean_apply_4(v_toBind_2618_, lean_box(0), lean_box(0), v___x_2634_, v___f_2632_);
return v___x_2635_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec_ref(v___f_2628_);
lean_dec_ref_known(v_givenNameView_2621_, 4);
v___x_2636_ = lean_box(0);
v___x_2637_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2627_, v_projs_2612_, v_inst_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v_inst_2608_, v_view_2609_, v_findLocalDecl_x3f_2610_, v_pre_2626_, v___x_2636_, v_globalDeclFound_2613_);
return v___x_2637_;
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_inc(v_toPure_2619_);
lean_dec_ref_known(v_givenNameView_2621_, 4);
lean_dec(v_projs_2612_);
lean_dec(v_n_2611_);
lean_dec_ref(v_findLocalDecl_x3f_2610_);
lean_dec_ref(v_view_2609_);
lean_dec(v_inst_2608_);
lean_dec_ref(v_inst_2607_);
lean_dec(v_inst_2606_);
lean_dec_ref(v_inst_2605_);
lean_dec_ref(v_inst_2604_);
lean_dec_ref(v_inst_2603_);
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_apply_2(v_toPure_2619_, lean_box(0), v___x_2638_);
return v___x_2639_;
}
}
else
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2656_; 
lean_inc(v_toPure_2619_);
lean_dec_ref_known(v_givenNameView_2621_, 4);
lean_dec(v_n_2611_);
lean_dec_ref(v_findLocalDecl_x3f_2610_);
lean_dec_ref(v_view_2609_);
lean_dec(v_inst_2608_);
lean_dec_ref(v_inst_2607_);
lean_dec(v_inst_2606_);
lean_dec_ref(v_inst_2605_);
lean_dec_ref(v_inst_2604_);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_inst_2603_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; lean_object* v_unused_2658_; 
v_unused_2657_ = lean_ctor_get(v_inst_2603_, 1);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_inst_2603_, 0);
lean_dec(v_unused_2658_);
v___x_2641_ = v_inst_2603_;
v_isShared_2642_ = v_isSharedCheck_2656_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v_inst_2603_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2656_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_val_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2655_; 
v_val_2643_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2645_ = v___x_2625_;
v_isShared_2646_ = v_isSharedCheck_2655_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_val_2643_);
lean_dec(v___x_2625_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2655_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = l_Lean_LocalDecl_toExpr(v_val_2643_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v_projs_2612_);
lean_ctor_set(v___x_2641_, 0, v___x_2647_);
v___x_2649_ = v___x_2641_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_projs_2612_);
v___x_2649_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2649_);
v___x_2651_ = v___x_2645_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_apply_2(v_toPure_2619_, lean_box(0), v___x_2651_);
return v___x_2652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2661_, lean_object* v_projs_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_view_2669_, lean_object* v_findLocalDecl_x3f_2670_, lean_object* v_pre_2671_, lean_object* v_____r_2672_, uint8_t v_globalDeclFoundNext_2673_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_str_2661_);
lean_ctor_set(v___x_2674_, 1, v_projs_2662_);
v___x_2675_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2663_, v_inst_2664_, v_inst_2665_, v_inst_2666_, v_inst_2667_, v_inst_2668_, v_view_2669_, v_findLocalDecl_x3f_2670_, v_pre_2671_, v___x_2674_, v_globalDeclFoundNext_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_view_2682_, lean_object* v_findLocalDecl_x3f_2683_, lean_object* v_n_2684_, lean_object* v_projs_2685_, lean_object* v_globalDeclFound_2686_){
_start:
{
uint8_t v_globalDeclFound_boxed_2687_; lean_object* v_res_2688_; 
v_globalDeclFound_boxed_2687_ = lean_unbox(v_globalDeclFound_2686_);
v_res_2688_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_view_2682_, v_findLocalDecl_x3f_2683_, v_n_2684_, v_projs_2685_, v_globalDeclFound_boxed_2687_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_view_2696_, lean_object* v_findLocalDecl_x3f_2697_, lean_object* v_n_2698_, lean_object* v_projs_2699_, uint8_t v_globalDeclFound_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v_inst_2695_, v_view_2696_, v_findLocalDecl_x3f_2697_, v_n_2698_, v_projs_2699_, v_globalDeclFound_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_view_2709_, lean_object* v_findLocalDecl_x3f_2710_, lean_object* v_n_2711_, lean_object* v_projs_2712_, lean_object* v_globalDeclFound_2713_){
_start:
{
uint8_t v_globalDeclFound_boxed_2714_; lean_object* v_res_2715_; 
v_globalDeclFound_boxed_2714_ = lean_unbox(v_globalDeclFound_2713_);
v_res_2715_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_view_2709_, v_findLocalDecl_x3f_2710_, v_n_2711_, v_projs_2712_, v_globalDeclFound_boxed_2714_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2716_, lean_object* v_givenNameView_2717_, lean_object* v_fullDeclName_2718_, lean_object* v_ns_2719_){
_start:
{
lean_object* v_name_2720_; lean_object* v_imported_2721_; lean_object* v_ctx_2722_; lean_object* v_scopes_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v_name_2720_ = lean_ctor_get(v_givenNameView_2717_, 0);
v_imported_2721_ = lean_ctor_get(v_givenNameView_2717_, 1);
v_ctx_2722_ = lean_ctor_get(v_givenNameView_2717_, 2);
v_scopes_2723_ = lean_ctor_get(v_givenNameView_2717_, 3);
lean_inc(v_name_2720_);
lean_inc(v_ns_2719_);
v___x_2724_ = l_Lean_Name_append(v_ns_2719_, v_name_2720_);
lean_inc(v_scopes_2723_);
lean_inc(v_ctx_2722_);
lean_inc(v_imported_2721_);
v___x_2725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_imported_2721_);
lean_ctor_set(v___x_2725_, 2, v_ctx_2722_);
lean_ctor_set(v___x_2725_, 3, v_scopes_2723_);
v___x_2726_ = l_Lean_MacroScopesView_review(v___x_2725_);
v___x_2727_ = lean_name_eq(v___x_2726_, v_fullDeclName_2718_);
lean_dec(v___x_2726_);
if (v___x_2727_ == 0)
{
if (lean_obj_tag(v_ns_2719_) == 1)
{
lean_object* v_pre_2728_; 
v_pre_2728_ = lean_ctor_get(v_ns_2719_, 0);
lean_inc(v_pre_2728_);
lean_dec_ref_known(v_ns_2719_, 2);
v_ns_2719_ = v_pre_2728_;
goto _start;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_ns_2719_);
lean_dec_ref(v_givenNameView_2717_);
lean_dec_ref(v_localDecl_2716_);
v___x_2730_ = lean_box(0);
return v___x_2730_;
}
}
else
{
lean_object* v___x_2731_; 
lean_dec(v_ns_2719_);
lean_dec_ref(v_givenNameView_2717_);
v___x_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_localDecl_2716_);
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2732_, lean_object* v_givenNameView_2733_, lean_object* v_fullDeclName_2734_, lean_object* v_ns_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2732_, v_givenNameView_2733_, v_fullDeclName_2734_, v_ns_2735_);
lean_dec(v_fullDeclName_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2737_, lean_object* v_givenName_2738_){
_start:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = l_Lean_LocalDecl_userName(v_localDecl_2737_);
v___x_2740_ = lean_name_eq(v___x_2739_, v_givenName_2738_);
lean_dec(v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_dec_ref(v_localDecl_2737_);
v___x_2741_ = lean_box(0);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_localDecl_2737_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2743_, lean_object* v_givenName_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2743_, v_givenName_2744_);
lean_dec(v_givenName_2744_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2746_, lean_object* v_givenName_2747_, uint8_t v_skipAuxDecl_2748_, lean_object* v___f_2749_, lean_object* v_auxDeclToFullName_2750_, lean_object* v_currNamespace_2751_, lean_object* v_givenNameView_2752_, lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
lean_dec_ref(v_givenNameView_2752_);
lean_dec(v_currNamespace_2751_);
lean_dec(v_auxDeclToFullName_2750_);
lean_dec_ref(v___f_2749_);
lean_dec(v_givenName_2747_);
lean_dec_ref(v_matchLocalDecl_x3f_2746_);
return v_x_2753_;
}
else
{
lean_object* v_val_2754_; uint8_t v___x_2755_; 
v_val_2754_ = lean_ctor_get(v_x_2753_, 0);
v___x_2755_ = l_Lean_LocalDecl_isAuxDecl(v_val_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; 
lean_inc(v_val_2754_);
lean_dec_ref_known(v_x_2753_, 1);
lean_dec_ref(v_givenNameView_2752_);
lean_dec(v_currNamespace_2751_);
lean_dec(v_auxDeclToFullName_2750_);
lean_dec_ref(v___f_2749_);
v___x_2756_ = lean_apply_2(v_matchLocalDecl_x3f_2746_, v_val_2754_, v_givenName_2747_);
return v___x_2756_;
}
else
{
if (v_skipAuxDecl_2748_ == 0)
{
if (v___x_2755_ == 0)
{
lean_object* v___x_2757_; 
lean_dec_ref_known(v_x_2753_, 1);
lean_dec_ref(v_givenNameView_2752_);
lean_dec(v_currNamespace_2751_);
lean_dec(v_auxDeclToFullName_2750_);
lean_dec_ref(v___f_2749_);
lean_dec(v_givenName_2747_);
lean_dec_ref(v_matchLocalDecl_x3f_2746_);
v___x_2757_ = lean_box(0);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = l_Lean_LocalDecl_fvarId(v_val_2754_);
v___x_2759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2749_, v_auxDeclToFullName_2750_, v___x_2758_);
if (lean_obj_tag(v___x_2759_) == 1)
{
lean_object* v_val_2760_; lean_object* v_fullDeclView_2761_; lean_object* v___y_2763_; lean_object* v_name_2784_; lean_object* v___x_2785_; 
lean_dec(v_givenName_2747_);
lean_dec_ref(v_matchLocalDecl_x3f_2746_);
v_val_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_val_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v_fullDeclView_2761_ = l_Lean_extractMacroScopes(v_val_2760_);
v_name_2784_ = lean_ctor_get(v_fullDeclView_2761_, 0);
lean_inc_n(v_name_2784_, 2);
v___x_2785_ = l_Lean_privateToUserName_x3f(v_name_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
v___y_2763_ = v_name_2784_;
goto v___jp_2762_;
}
else
{
lean_object* v_val_2786_; 
lean_dec(v_name_2784_);
v_val_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___y_2763_ = v_val_2786_;
goto v___jp_2762_;
}
v___jp_2762_:
{
lean_object* v_imported_2764_; lean_object* v_ctx_2765_; lean_object* v_scopes_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2782_; 
v_imported_2764_ = lean_ctor_get(v_fullDeclView_2761_, 1);
v_ctx_2765_ = lean_ctor_get(v_fullDeclView_2761_, 2);
v_scopes_2766_ = lean_ctor_get(v_fullDeclView_2761_, 3);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_fullDeclView_2761_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; 
v_unused_2783_ = lean_ctor_get(v_fullDeclView_2761_, 0);
lean_dec(v_unused_2783_);
v___x_2768_ = v_fullDeclView_2761_;
v_isShared_2769_ = v_isSharedCheck_2782_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_scopes_2766_);
lean_inc(v_ctx_2765_);
lean_inc(v_imported_2764_);
lean_dec(v_fullDeclView_2761_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2782_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_fullDeclView_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___y_2763_);
v_fullDeclView_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___y_2763_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_imported_2764_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_ctx_2765_);
lean_ctor_set(v_reuseFailAlloc_2781_, 3, v_scopes_2766_);
v_fullDeclView_2771_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v_fullDeclName_2772_; uint8_t v___x_2773_; 
lean_inc_ref(v_fullDeclView_2771_);
v_fullDeclName_2772_ = l_Lean_MacroScopesView_review(v_fullDeclView_2771_);
v___x_2773_ = l_Lean_Name_isPrefixOf(v_currNamespace_2751_, v_fullDeclName_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
lean_inc(v_val_2754_);
lean_dec_ref(v_fullDeclView_2771_);
lean_dec_ref_known(v_x_2753_, 1);
v___x_2774_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2754_, v_givenNameView_2752_, v_fullDeclName_2772_, v_currNamespace_2751_);
lean_dec(v_fullDeclName_2772_);
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; lean_object* v_localDeclNameView_2776_; uint8_t v___x_2777_; 
lean_dec(v_fullDeclName_2772_);
lean_dec(v_currNamespace_2751_);
v___x_2775_ = l_Lean_LocalDecl_userName(v_val_2754_);
v_localDeclNameView_2776_ = l_Lean_extractMacroScopes(v___x_2775_);
v___x_2777_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2776_, v_givenNameView_2752_);
lean_dec_ref(v_localDeclNameView_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
lean_dec_ref(v_fullDeclView_2771_);
lean_dec_ref_known(v_x_2753_, 1);
lean_dec_ref(v_givenNameView_2752_);
v___x_2778_ = lean_box(0);
return v___x_2778_;
}
else
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2752_, v_fullDeclView_2771_);
lean_dec_ref(v_fullDeclView_2771_);
lean_dec_ref(v_givenNameView_2752_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref_known(v_x_2753_, 1);
v___x_2780_ = lean_box(0);
return v___x_2780_;
}
else
{
return v_x_2753_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2787_; 
lean_inc(v_val_2754_);
lean_dec(v___x_2759_);
lean_dec_ref_known(v_x_2753_, 1);
lean_dec_ref(v_givenNameView_2752_);
lean_dec(v_currNamespace_2751_);
v___x_2787_ = lean_apply_2(v_matchLocalDecl_x3f_2746_, v_val_2754_, v_givenName_2747_);
return v___x_2787_;
}
}
}
else
{
lean_object* v___x_2788_; 
lean_dec_ref_known(v_x_2753_, 1);
lean_dec_ref(v_givenNameView_2752_);
lean_dec(v_currNamespace_2751_);
lean_dec(v_auxDeclToFullName_2750_);
lean_dec_ref(v___f_2749_);
lean_dec(v_givenName_2747_);
lean_dec_ref(v_matchLocalDecl_x3f_2746_);
v___x_2788_ = lean_box(0);
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2789_, lean_object* v_givenName_2790_, lean_object* v_skipAuxDecl_2791_, lean_object* v___f_2792_, lean_object* v_auxDeclToFullName_2793_, lean_object* v_currNamespace_2794_, lean_object* v_givenNameView_2795_, lean_object* v_x_2796_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2797_; lean_object* v_res_2798_; 
v_skipAuxDecl_boxed_2797_ = lean_unbox(v_skipAuxDecl_2791_);
v_res_2798_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2789_, v_givenName_2790_, v_skipAuxDecl_boxed_2797_, v___f_2792_, v_auxDeclToFullName_2793_, v_currNamespace_2794_, v_givenNameView_2795_, v_x_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2799_, lean_object* v_matchLocalDecl_x3f_2800_, lean_object* v_givenName_2801_, lean_object* v_x_2802_){
_start:
{
if (lean_obj_tag(v_x_2802_) == 0)
{
lean_dec(v_givenName_2801_);
lean_dec_ref(v_matchLocalDecl_x3f_2800_);
return v_x_2802_;
}
else
{
lean_object* v_val_2803_; uint8_t v___x_2804_; 
v_val_2803_ = lean_ctor_get(v_x_2802_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v_x_2802_, 1);
v___x_2804_ = l_Lean_LocalDecl_isAuxDecl(v_val_2803_);
if (v___x_2804_ == 0)
{
lean_dec(v_val_2803_);
lean_dec(v_givenName_2801_);
lean_dec_ref(v_matchLocalDecl_x3f_2800_);
lean_inc(v_localDecl_x3f_2799_);
return v_localDecl_x3f_2799_;
}
else
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_apply_2(v_matchLocalDecl_x3f_2800_, v_val_2803_, v_givenName_2801_);
return v___x_2805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2806_, lean_object* v_matchLocalDecl_x3f_2807_, lean_object* v_givenName_2808_, lean_object* v_x_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2806_, v_matchLocalDecl_x3f_2807_, v_givenName_2808_, v_x_2809_);
lean_dec(v_localDecl_x3f_2806_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2830_, lean_object* v_matchLocalDecl_x3f_2831_, lean_object* v___f_2832_, lean_object* v_auxDeclToFullName_2833_, lean_object* v_currNamespace_2834_, lean_object* v_givenNameView_2835_, uint8_t v_skipAuxDecl_2836_){
_start:
{
lean_object* v_decls_2837_; lean_object* v_givenName_2838_; lean_object* v___x_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; lean_object* v_localDecl_x3f_2842_; 
v_decls_2837_ = lean_ctor_get(v_lctx_2830_, 1);
lean_inc_ref_n(v_decls_2837_, 2);
lean_dec_ref(v_lctx_2830_);
lean_inc_ref(v_givenNameView_2835_);
v_givenName_2838_ = l_Lean_MacroScopesView_review(v_givenNameView_2835_);
v___x_2839_ = lean_box(v_skipAuxDecl_2836_);
lean_inc(v_givenName_2838_);
lean_inc_ref(v_matchLocalDecl_x3f_2831_);
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2840_, 0, v_matchLocalDecl_x3f_2831_);
lean_closure_set(v___f_2840_, 1, v_givenName_2838_);
lean_closure_set(v___f_2840_, 2, v___x_2839_);
lean_closure_set(v___f_2840_, 3, v___f_2832_);
lean_closure_set(v___f_2840_, 4, v_auxDeclToFullName_2833_);
lean_closure_set(v___f_2840_, 5, v_currNamespace_2834_);
lean_closure_set(v___f_2840_, 6, v_givenNameView_2835_);
v___x_2841_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2842_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2841_, v_decls_2837_, v___f_2840_);
if (lean_obj_tag(v_localDecl_x3f_2842_) == 0)
{
if (v_skipAuxDecl_2836_ == 0)
{
lean_object* v___f_2843_; lean_object* v___x_2844_; 
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2843_, 0, v_localDecl_x3f_2842_);
lean_closure_set(v___f_2843_, 1, v_matchLocalDecl_x3f_2831_);
lean_closure_set(v___f_2843_, 2, v_givenName_2838_);
v___x_2844_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2841_, v_decls_2837_, v___f_2843_);
return v___x_2844_;
}
else
{
lean_dec(v_givenName_2838_);
lean_dec_ref(v_decls_2837_);
lean_dec_ref(v_matchLocalDecl_x3f_2831_);
return v_localDecl_x3f_2842_;
}
}
else
{
lean_dec(v_givenName_2838_);
lean_dec_ref(v_decls_2837_);
lean_dec_ref(v_matchLocalDecl_x3f_2831_);
return v_localDecl_x3f_2842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2845_, lean_object* v_matchLocalDecl_x3f_2846_, lean_object* v___f_2847_, lean_object* v_auxDeclToFullName_2848_, lean_object* v_currNamespace_2849_, lean_object* v_givenNameView_2850_, lean_object* v_skipAuxDecl_2851_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2852_; lean_object* v_res_2853_; 
v_skipAuxDecl_boxed_2852_ = lean_unbox(v_skipAuxDecl_2851_);
v_res_2853_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2845_, v_matchLocalDecl_x3f_2846_, v___f_2847_, v_auxDeclToFullName_2848_, v_currNamespace_2849_, v_givenNameView_2850_, v_skipAuxDecl_boxed_2852_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2854_, lean_object* v_lctx_2855_, lean_object* v_matchLocalDecl_x3f_2856_, lean_object* v___f_2857_, lean_object* v_auxDeclToFullName_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_currNamespace_2865_){
_start:
{
lean_object* v_view_2866_; lean_object* v_name_2867_; lean_object* v_findLocalDecl_x3f_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; 
v_view_2866_ = l_Lean_extractMacroScopes(v_n_2854_);
v_name_2867_ = lean_ctor_get(v_view_2866_, 0);
lean_inc(v_name_2867_);
v_findLocalDecl_x3f_2868_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2868_, 0, v_lctx_2855_);
lean_closure_set(v_findLocalDecl_x3f_2868_, 1, v_matchLocalDecl_x3f_2856_);
lean_closure_set(v_findLocalDecl_x3f_2868_, 2, v___f_2857_);
lean_closure_set(v_findLocalDecl_x3f_2868_, 3, v_auxDeclToFullName_2858_);
lean_closure_set(v_findLocalDecl_x3f_2868_, 4, v_currNamespace_2865_);
v___x_2869_ = lean_box(0);
v___x_2870_ = 0;
v___x_2871_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2859_, v_inst_2860_, v_inst_2861_, v_inst_2862_, v_inst_2863_, v_inst_2864_, v_view_2866_, v_findLocalDecl_x3f_2868_, v_name_2867_, v___x_2869_, v___x_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2872_, lean_object* v_n_2873_, lean_object* v_lctx_2874_, lean_object* v_matchLocalDecl_x3f_2875_, lean_object* v___f_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_inst_2881_, lean_object* v_toBind_2882_, lean_object* v_____do__lift_2883_){
_start:
{
lean_object* v_auxDeclToFullName_2884_; lean_object* v_getCurrNamespace_2885_; lean_object* v___f_2886_; lean_object* v___x_2887_; 
v_auxDeclToFullName_2884_ = lean_ctor_get(v_____do__lift_2883_, 2);
lean_inc(v_auxDeclToFullName_2884_);
lean_dec_ref(v_____do__lift_2883_);
v_getCurrNamespace_2885_ = lean_ctor_get(v_inst_2872_, 0);
lean_inc(v_getCurrNamespace_2885_);
v___f_2886_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2886_, 0, v_n_2873_);
lean_closure_set(v___f_2886_, 1, v_lctx_2874_);
lean_closure_set(v___f_2886_, 2, v_matchLocalDecl_x3f_2875_);
lean_closure_set(v___f_2886_, 3, v___f_2876_);
lean_closure_set(v___f_2886_, 4, v_auxDeclToFullName_2884_);
lean_closure_set(v___f_2886_, 5, v_inst_2877_);
lean_closure_set(v___f_2886_, 6, v_inst_2872_);
lean_closure_set(v___f_2886_, 7, v_inst_2878_);
lean_closure_set(v___f_2886_, 8, v_inst_2879_);
lean_closure_set(v___f_2886_, 9, v_inst_2880_);
lean_closure_set(v___f_2886_, 10, v_inst_2881_);
v___x_2887_ = lean_apply_4(v_toBind_2882_, lean_box(0), lean_box(0), v_getCurrNamespace_2885_, v___f_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2888_, lean_object* v_n_2889_, lean_object* v_matchLocalDecl_x3f_2890_, lean_object* v___f_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_toBind_2897_, lean_object* v_inst_2898_, lean_object* v_lctx_2899_){
_start:
{
lean_object* v___f_2900_; lean_object* v___x_2901_; 
lean_inc(v_toBind_2897_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2900_, 0, v_inst_2888_);
lean_closure_set(v___f_2900_, 1, v_n_2889_);
lean_closure_set(v___f_2900_, 2, v_lctx_2899_);
lean_closure_set(v___f_2900_, 3, v_matchLocalDecl_x3f_2890_);
lean_closure_set(v___f_2900_, 4, v___f_2891_);
lean_closure_set(v___f_2900_, 5, v_inst_2892_);
lean_closure_set(v___f_2900_, 6, v_inst_2893_);
lean_closure_set(v___f_2900_, 7, v_inst_2894_);
lean_closure_set(v___f_2900_, 8, v_inst_2895_);
lean_closure_set(v___f_2900_, 9, v_inst_2896_);
lean_closure_set(v___f_2900_, 10, v_toBind_2897_);
v___x_2901_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v_inst_2898_, v___f_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_n_2911_){
_start:
{
lean_object* v_toBind_2912_; lean_object* v___f_2913_; lean_object* v_matchLocalDecl_x3f_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; 
v_toBind_2912_ = lean_ctor_get(v_inst_2904_, 1);
lean_inc_n(v_toBind_2912_, 2);
v___f_2913_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2914_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2910_);
v___f_2915_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2915_, 0, v_inst_2905_);
lean_closure_set(v___f_2915_, 1, v_n_2911_);
lean_closure_set(v___f_2915_, 2, v_matchLocalDecl_x3f_2914_);
lean_closure_set(v___f_2915_, 3, v___f_2913_);
lean_closure_set(v___f_2915_, 4, v_inst_2904_);
lean_closure_set(v___f_2915_, 5, v_inst_2906_);
lean_closure_set(v___f_2915_, 6, v_inst_2907_);
lean_closure_set(v___f_2915_, 7, v_inst_2908_);
lean_closure_set(v___f_2915_, 8, v_inst_2909_);
lean_closure_set(v___f_2915_, 9, v_toBind_2912_);
lean_closure_set(v___f_2915_, 10, v_inst_2910_);
v___x_2916_ = lean_apply_4(v_toBind_2912_, lean_box(0), lean_box(0), v_inst_2910_, v___f_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_n_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_resolveLocalName___redArg(v_inst_2918_, v_inst_2919_, v_inst_2920_, v_inst_2921_, v_inst_2922_, v_inst_2923_, v_inst_2924_, v_n_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2927_, uint8_t v_____do__lift_2928_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_box(v_____do__lift_2928_);
v___x_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
v___x_2931_ = lean_apply_2(v_toPure_2927_, lean_box(0), v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2932_, lean_object* v_____do__lift_2933_){
_start:
{
uint8_t v_____do__lift_1059__boxed_2934_; lean_object* v_res_2935_; 
v_____do__lift_1059__boxed_2934_ = lean_unbox(v_____do__lift_2933_);
v_res_2935_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2932_, v_____do__lift_1059__boxed_2934_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2936_, lean_object* v___y_2937_, lean_object* v_____do__lift_2938_){
_start:
{
if (lean_obj_tag(v_____do__lift_2938_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_dec(v___y_2937_);
v___x_2939_ = lean_box(0);
v___x_2940_ = lean_apply_2(v_toPure_2936_, lean_box(0), v___x_2939_);
return v___x_2940_;
}
else
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2948_; 
v_isSharedCheck_2948_ = !lean_is_exclusive(v_____do__lift_2938_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; 
v_unused_2949_ = lean_ctor_get(v_____do__lift_2938_, 0);
lean_dec(v_unused_2949_);
v___x_2942_ = v_____do__lift_2938_;
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v_____do__lift_2938_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___y_2937_);
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___y_2937_);
v___x_2945_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_apply_2(v_toPure_2936_, lean_box(0), v___x_2945_);
return v___x_2946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2952_, lean_object* v_toBind_2953_, lean_object* v___f_2954_, lean_object* v_____do__lift_2955_){
_start:
{
if (lean_obj_tag(v_____do__lift_2955_) == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v___f_2954_);
lean_dec(v_toBind_2953_);
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2956_);
return v___x_2957_;
}
else
{
lean_object* v_val_2958_; uint8_t v___x_2959_; 
v_val_2958_ = lean_ctor_get(v_____do__lift_2955_, 0);
v___x_2959_ = lean_unbox(v_val_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2960_);
v___x_2962_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2961_, v___f_2954_);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2964_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2963_);
v___x_2965_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2964_, v___f_2954_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2966_, lean_object* v_toBind_2967_, lean_object* v___f_2968_, lean_object* v_____do__lift_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2966_, v_toBind_2967_, v___f_2968_, v_____do__lift_2969_);
lean_dec(v_____do__lift_2969_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2971_, lean_object* v_filter_2972_, lean_object* v___y_2973_, lean_object* v_toBind_2974_, lean_object* v___f_2975_, lean_object* v___f_2976_, lean_object* v_____do__lift_2977_){
_start:
{
if (lean_obj_tag(v_____do__lift_2977_) == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec(v___f_2976_);
lean_dec(v___f_2975_);
lean_dec(v_toBind_2974_);
lean_dec(v___y_2973_);
lean_dec(v_filter_2972_);
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_apply_2(v_toPure_2971_, lean_box(0), v___x_2978_);
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec(v_toPure_2971_);
v___x_2980_ = lean_apply_1(v_filter_2972_, v___y_2973_);
lean_inc(v_toBind_2974_);
v___x_2981_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2980_, v___f_2975_);
v___x_2982_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2981_, v___f_2976_);
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_2983_, lean_object* v_filter_2984_, lean_object* v___y_2985_, lean_object* v_toBind_2986_, lean_object* v___f_2987_, lean_object* v___f_2988_, lean_object* v_____do__lift_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_2983_, v_filter_2984_, v___y_2985_, v_toBind_2986_, v___f_2987_, v___f_2988_, v_____do__lift_2989_);
lean_dec(v_____do__lift_2989_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_2991_, lean_object* v_n_u2080_2992_, lean_object* v_toBind_2993_, lean_object* v___f_2994_, lean_object* v_____do__lift_2995_){
_start:
{
if (lean_obj_tag(v_____do__lift_2995_) == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v___f_2994_);
lean_dec(v_toBind_2993_);
v___x_2999_ = lean_box(0);
v___x_3000_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2999_);
return v___x_3000_;
}
else
{
lean_object* v_val_3001_; 
v_val_3001_ = lean_ctor_get(v_____do__lift_2995_, 0);
if (lean_obj_tag(v_val_3001_) == 1)
{
lean_object* v_tail_3002_; 
v_tail_3002_ = lean_ctor_get(v_val_3001_, 1);
if (lean_obj_tag(v_tail_3002_) == 0)
{
lean_object* v_head_3003_; lean_object* v_fst_3004_; uint8_t v___x_3005_; 
v_head_3003_ = lean_ctor_get(v_val_3001_, 0);
v_fst_3004_ = lean_ctor_get(v_head_3003_, 0);
v___x_3005_ = lean_name_eq(v_fst_3004_, v_n_u2080_2992_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_3006_);
v___x_3008_ = lean_apply_4(v_toBind_2993_, lean_box(0), lean_box(0), v___x_3007_, v___f_2994_);
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3010_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_3009_);
v___x_3011_ = lean_apply_4(v_toBind_2993_, lean_box(0), lean_box(0), v___x_3010_, v___f_2994_);
return v___x_3011_;
}
}
else
{
lean_dec(v___f_2994_);
lean_dec(v_toBind_2993_);
goto v___jp_2996_;
}
}
else
{
lean_dec(v___f_2994_);
lean_dec(v_toBind_2993_);
goto v___jp_2996_;
}
}
v___jp_2996_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2997_);
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3012_, lean_object* v_n_u2080_3013_, lean_object* v_toBind_3014_, lean_object* v___f_3015_, lean_object* v_____do__lift_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3012_, v_n_u2080_3013_, v_toBind_3014_, v___f_3015_, v_____do__lift_3016_);
lean_dec(v_____do__lift_3016_);
lean_dec(v_n_u2080_3013_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_n_u2080_3024_, lean_object* v_filter_3025_, lean_object* v_view_x3f_3026_, lean_object* v_n_3027_){
_start:
{
lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v_toApplicative_3040_; lean_object* v_getEnv_3041_; lean_object* v_modifyEnv_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3080_; 
lean_inc_ref_n(v_inst_3018_, 8);
v___f_3028_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3028_, 0, v_inst_3018_);
v___f_3029_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3029_, 0, v_inst_3018_);
v___f_3030_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3030_, 0, v_inst_3018_);
v___f_3031_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3031_, 0, v_inst_3018_);
v___f_3032_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3032_, 0, v_inst_3018_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___f_3028_);
lean_ctor_set(v___x_3033_, 1, v___f_3029_);
v___x_3034_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3034_, 0, lean_box(0));
lean_closure_set(v___x_3034_, 1, v_inst_3018_);
v___x_3035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_ctor_set(v___x_3035_, 2, v___f_3030_);
lean_ctor_set(v___x_3035_, 3, v___f_3031_);
lean_ctor_set(v___x_3035_, 4, v___f_3032_);
v___x_3036_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3036_, 0, lean_box(0));
lean_closure_set(v___x_3036_, 1, v_inst_3018_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3038_, 0, lean_box(0));
lean_closure_set(v___x_3038_, 1, v_inst_3018_);
lean_inc_ref(v___x_3038_);
v___x_3039_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3038_, v_inst_3019_);
v_toApplicative_3040_ = lean_ctor_get(v_inst_3018_, 0);
lean_inc_ref(v_toApplicative_3040_);
v_getEnv_3041_ = lean_ctor_get(v_inst_3020_, 0);
v_modifyEnv_3042_ = lean_ctor_get(v_inst_3020_, 1);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_inst_3020_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3044_ = v_inst_3020_;
v_isShared_3045_ = v_isSharedCheck_3080_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_modifyEnv_3042_);
lean_inc(v_getEnv_3041_);
lean_dec(v_inst_3020_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3080_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_toBind_3046_; lean_object* v_toPure_3047_; lean_object* v___f_3048_; lean_object* v___f_3049_; lean_object* v___f_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v_toBind_3046_ = lean_ctor_get(v_inst_3018_, 1);
lean_inc_n(v_toBind_3046_, 2);
lean_dec_ref(v_inst_3018_);
v_toPure_3047_ = lean_ctor_get(v_toApplicative_3040_, 1);
lean_inc_n(v_toPure_3047_, 3);
lean_dec_ref(v_toApplicative_3040_);
lean_inc_ref(v___x_3038_);
v___f_3048_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3048_, 0, v_modifyEnv_3042_);
lean_closure_set(v___f_3048_, 1, v___x_3038_);
v___f_3049_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3049_, 0, v_toPure_3047_);
v___f_3050_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3050_, 0, v_toPure_3047_);
lean_inc_ref(v___f_3050_);
v___x_3051_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v_getEnv_3041_, v___f_3050_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___f_3048_);
lean_ctor_set(v___x_3044_, 0, v___x_3051_);
v___x_3053_ = v___x_3044_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___f_3048_);
v___x_3053_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___f_3056_; lean_object* v___y_3058_; 
lean_inc(v_toBind_3046_);
v___x_3054_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v_inst_3021_, v___f_3050_);
lean_inc_ref(v___x_3038_);
v___x_3055_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3038_, v_inst_3022_);
v___f_3056_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3056_, 0, v_inst_3023_);
lean_closure_set(v___f_3056_, 1, v___x_3038_);
if (lean_obj_tag(v_view_x3f_3026_) == 1)
{
lean_object* v_val_3066_; lean_object* v_imported_3067_; lean_object* v_ctx_3068_; lean_object* v_scopes_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
v_val_3066_ = lean_ctor_get(v_view_x3f_3026_, 0);
lean_inc(v_val_3066_);
lean_dec_ref_known(v_view_x3f_3026_, 1);
v_imported_3067_ = lean_ctor_get(v_val_3066_, 1);
v_ctx_3068_ = lean_ctor_get(v_val_3066_, 2);
v_scopes_3069_ = lean_ctor_get(v_val_3066_, 3);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_val_3066_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v_val_3066_, 0);
lean_dec(v_unused_3078_);
v___x_3071_ = v_val_3066_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_scopes_3069_);
lean_inc(v_ctx_3068_);
lean_inc(v_imported_3067_);
lean_dec(v_val_3066_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v_n_3027_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_n_3027_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_imported_3067_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_ctx_3068_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_scopes_3069_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_MacroScopesView_review(v___x_3074_);
v___y_3058_ = v___x_3075_;
goto v___jp_3057_;
}
}
}
else
{
lean_dec(v_view_x3f_3026_);
v___y_3058_ = v_n_3027_;
goto v___jp_3057_;
}
v___jp_3057_:
{
lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___f_3061_; lean_object* v___f_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_inc_n(v___y_3058_, 2);
lean_inc_n(v_toPure_3047_, 3);
v___f_3059_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3059_, 0, v_toPure_3047_);
lean_closure_set(v___f_3059_, 1, v___y_3058_);
lean_inc_n(v_toBind_3046_, 3);
v___f_3060_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3060_, 0, v_toPure_3047_);
lean_closure_set(v___f_3060_, 1, v_toBind_3046_);
lean_closure_set(v___f_3060_, 2, v___f_3059_);
v___f_3061_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3061_, 0, v_toPure_3047_);
lean_closure_set(v___f_3061_, 1, v_filter_3025_);
lean_closure_set(v___f_3061_, 2, v___y_3058_);
lean_closure_set(v___f_3061_, 3, v_toBind_3046_);
lean_closure_set(v___f_3061_, 4, v___f_3049_);
lean_closure_set(v___f_3061_, 5, v___f_3060_);
v___f_3062_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3062_, 0, v_toPure_3047_);
lean_closure_set(v___f_3062_, 1, v_n_u2080_3024_);
lean_closure_set(v___f_3062_, 2, v_toBind_3046_);
lean_closure_set(v___f_3062_, 3, v___f_3061_);
v___x_3063_ = 0;
v___x_3064_ = l_Lean_resolveGlobalName___redArg(v___x_3037_, v___x_3039_, v___x_3053_, v___x_3054_, v___x_3055_, v___f_3056_, v___y_3058_, v___x_3063_);
v___x_3065_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v___x_3064_, v___f_3062_);
return v___x_3065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_n_u2080_3088_, lean_object* v_filter_3089_, lean_object* v_view_x3f_3090_, lean_object* v_n_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3082_, v_inst_3083_, v_inst_3084_, v_inst_3085_, v_inst_3086_, v_inst_3087_, v_n_u2080_3088_, v_filter_3089_, v_view_x3f_3090_, v_n_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3097_, lean_object* v_____x_3098_){
_start:
{
if (lean_obj_tag(v_____x_3098_) == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3100_ = lean_apply_2(v_toPure_3097_, lean_box(0), v___x_3099_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_apply_2(v_toPure_3097_, lean_box(0), v_____x_3098_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3102_, lean_object* v_____do__lift_3103_){
_start:
{
if (lean_obj_tag(v_____do__lift_3103_) == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_apply_2(v_toPure_3102_, lean_box(0), v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v_val_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3115_; 
v_val_3106_ = lean_ctor_get(v_____do__lift_3103_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_____do__lift_3103_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3108_ = v_____do__lift_3103_;
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_val_3106_);
lean_dec(v_____do__lift_3103_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v_val_3106_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3110_);
v___x_3112_ = v___x_3108_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_apply_2(v_toPure_3102_, lean_box(0), v___x_3112_);
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3116_, lean_object* v___x_3117_, lean_object* v_____do__lift_3118_){
_start:
{
if (lean_obj_tag(v_____do__lift_3118_) == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_apply_2(v_toPure_3116_, lean_box(0), v___x_3117_);
return v___x_3119_;
}
else
{
lean_object* v_val_3120_; lean_object* v_fst_3121_; lean_object* v___x_3122_; 
lean_dec(v___x_3117_);
v_val_3120_ = lean_ctor_get(v_____do__lift_3118_, 0);
lean_inc(v_val_3120_);
lean_dec_ref_known(v_____do__lift_3118_, 1);
v_fst_3121_ = lean_ctor_get(v_val_3120_, 0);
lean_inc(v_fst_3121_);
lean_dec(v_val_3120_);
v___x_3122_ = lean_apply_2(v_toPure_3116_, lean_box(0), v_fst_3121_);
return v___x_3122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3123_, lean_object* v___x_3124_, lean_object* v___x_3125_, lean_object* v_____do__lift_3126_){
_start:
{
if (lean_obj_tag(v_____do__lift_3126_) == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec(v___x_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v___x_3128_ = lean_apply_2(v_toPure_3123_, lean_box(0), v___x_3127_);
return v___x_3128_;
}
else
{
lean_object* v_val_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3160_; 
v_val_3129_ = lean_ctor_get(v_____do__lift_3126_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_____do__lift_3126_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3131_ = v_____do__lift_3126_;
v_isShared_3132_ = v_isSharedCheck_3160_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_val_3129_);
lean_dec(v_____do__lift_3126_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3160_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
if (lean_obj_tag(v_val_3129_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___x_3125_);
v_a_3133_ = lean_ctor_get(v_val_3129_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_val_3129_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3135_ = v_val_3129_;
v_isShared_3136_ = v_isSharedCheck_3146_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v_val_3129_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3146_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_a_3133_);
v___x_3138_ = v___x_3131_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v___x_3124_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3139_);
v___x_3141_ = v___x_3135_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
v___x_3143_ = lean_apply_2(v_toPure_3123_, lean_box(0), v___x_3142_);
return v___x_3143_;
}
}
}
}
else
{
lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3158_; 
v_isSharedCheck_3158_ = !lean_is_exclusive(v_val_3129_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v_val_3129_, 0);
lean_dec(v_unused_3159_);
v___x_3148_ = v_val_3129_;
v_isShared_3149_ = v_isSharedCheck_3158_;
goto v_resetjp_3147_;
}
else
{
lean_dec(v_val_3129_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3158_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3125_);
lean_ctor_set(v___x_3150_, 1, v___x_3124_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v___x_3150_);
v___x_3152_ = v___x_3148_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3154_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3152_);
v___x_3154_ = v___x_3131_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_apply_2(v_toPure_3123_, lean_box(0), v___x_3154_);
return v___x_3155_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3161_, lean_object* v___x_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_n_u2080_3169_, lean_object* v_filter_3170_, lean_object* v_view_x3f_3171_, lean_object* v_toBind_3172_, lean_object* v___f_3173_, lean_object* v___f_3174_, lean_object* v_a_3175_, lean_object* v_x_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_snd_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_snd_3178_ = lean_ctor_get(v___y_3177_, 1);
lean_inc(v_snd_3178_);
lean_dec_ref(v___y_3177_);
v___x_3179_ = l_Lean_Name_appendCore(v_a_3175_, v_snd_3178_);
lean_inc(v___x_3179_);
v___f_3180_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3180_, 0, v_toPure_3161_);
lean_closure_set(v___f_3180_, 1, v___x_3179_);
lean_closure_set(v___f_3180_, 2, v___x_3162_);
v___x_3181_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3163_, v_inst_3164_, v_inst_3165_, v_inst_3166_, v_inst_3167_, v_inst_3168_, v_n_u2080_3169_, v_filter_3170_, v_view_x3f_3171_, v___x_3179_);
lean_inc_n(v_toBind_3172_, 2);
v___x_3182_ = lean_apply_4(v_toBind_3172_, lean_box(0), lean_box(0), v___x_3181_, v___f_3173_);
v___x_3183_ = lean_apply_4(v_toBind_3172_, lean_box(0), lean_box(0), v___x_3182_, v___f_3174_);
v___x_3184_ = lean_apply_4(v_toBind_3172_, lean_box(0), lean_box(0), v___x_3183_, v___f_3180_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3185_ = _args[0];
lean_object* v___x_3186_ = _args[1];
lean_object* v_inst_3187_ = _args[2];
lean_object* v_inst_3188_ = _args[3];
lean_object* v_inst_3189_ = _args[4];
lean_object* v_inst_3190_ = _args[5];
lean_object* v_inst_3191_ = _args[6];
lean_object* v_inst_3192_ = _args[7];
lean_object* v_n_u2080_3193_ = _args[8];
lean_object* v_filter_3194_ = _args[9];
lean_object* v_view_x3f_3195_ = _args[10];
lean_object* v_toBind_3196_ = _args[11];
lean_object* v___f_3197_ = _args[12];
lean_object* v___f_3198_ = _args[13];
lean_object* v_a_3199_ = _args[14];
lean_object* v_x_3200_ = _args[15];
lean_object* v___y_3201_ = _args[16];
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3185_, v___x_3186_, v_inst_3187_, v_inst_3188_, v_inst_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_n_u2080_3193_, v_filter_3194_, v_view_x3f_3195_, v_toBind_3196_, v___f_3197_, v___f_3198_, v_a_3199_, v_x_3200_, v___y_3201_);
lean_dec(v_a_3199_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3206_, lean_object* v_n_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_n_u2080_3214_, lean_object* v_filter_3215_, lean_object* v_view_x3f_3216_, lean_object* v_toBind_3217_, lean_object* v___f_3218_, lean_object* v___f_3219_, lean_object* v___x_3220_, lean_object* v_____do__lift_3221_){
_start:
{
if (lean_obj_tag(v_____do__lift_3221_) == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___x_3220_);
lean_dec(v___f_3219_);
lean_dec(v___f_3218_);
lean_dec(v_toBind_3217_);
lean_dec(v_view_x3f_3216_);
lean_dec(v_filter_3215_);
lean_dec(v_n_u2080_3214_);
lean_dec(v_inst_3213_);
lean_dec_ref(v_inst_3212_);
lean_dec(v_inst_3211_);
lean_dec_ref(v_inst_3210_);
lean_dec_ref(v_inst_3209_);
lean_dec_ref(v_inst_3208_);
lean_dec(v_n_3207_);
v___x_3222_ = lean_box(0);
v___x_3223_ = lean_apply_2(v_toPure_3206_, lean_box(0), v___x_3222_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___f_3227_; lean_object* v___f_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3224_ = l_Lean_privateToUserName(v_n_3207_);
v___x_3225_ = l_Lean_Name_componentsRev(v___x_3224_);
v___x_3226_ = lean_box(0);
lean_inc(v_toPure_3206_);
v___f_3227_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3227_, 0, v_toPure_3206_);
lean_closure_set(v___f_3227_, 1, v___x_3226_);
lean_inc(v_toBind_3217_);
v___f_3228_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3228_, 0, v_toPure_3206_);
lean_closure_set(v___f_3228_, 1, v___x_3226_);
lean_closure_set(v___f_3228_, 2, v_inst_3208_);
lean_closure_set(v___f_3228_, 3, v_inst_3209_);
lean_closure_set(v___f_3228_, 4, v_inst_3210_);
lean_closure_set(v___f_3228_, 5, v_inst_3211_);
lean_closure_set(v___f_3228_, 6, v_inst_3212_);
lean_closure_set(v___f_3228_, 7, v_inst_3213_);
lean_closure_set(v___f_3228_, 8, v_n_u2080_3214_);
lean_closure_set(v___f_3228_, 9, v_filter_3215_);
lean_closure_set(v___f_3228_, 10, v_view_x3f_3216_);
lean_closure_set(v___f_3228_, 11, v_toBind_3217_);
lean_closure_set(v___f_3228_, 12, v___f_3218_);
lean_closure_set(v___f_3228_, 13, v___f_3219_);
v___x_3229_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3230_ = l_List_forIn_x27_loop___redArg(v___x_3220_, v___f_3228_, v___x_3225_, v___x_3229_);
lean_dec(v___x_3225_);
v___x_3231_ = lean_apply_4(v_toBind_3217_, lean_box(0), lean_box(0), v___x_3230_, v___f_3227_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3232_, lean_object* v_n_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_n_u2080_3240_, lean_object* v_filter_3241_, lean_object* v_view_x3f_3242_, lean_object* v_toBind_3243_, lean_object* v___f_3244_, lean_object* v___f_3245_, lean_object* v___x_3246_, lean_object* v_____do__lift_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3232_, v_n_3233_, v_inst_3234_, v_inst_3235_, v_inst_3236_, v_inst_3237_, v_inst_3238_, v_inst_3239_, v_n_u2080_3240_, v_filter_3241_, v_view_x3f_3242_, v_toBind_3243_, v___f_3244_, v___f_3245_, v___x_3246_, v_____do__lift_3247_);
lean_dec(v_____do__lift_3247_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_inst_3254_, lean_object* v_n_u2080_3255_, lean_object* v_filter_3256_, lean_object* v_view_x3f_3257_, lean_object* v_n_3258_){
_start:
{
lean_object* v___f_3259_; lean_object* v___f_3260_; lean_object* v___f_3261_; lean_object* v___f_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___y_3270_; uint8_t v___x_3278_; 
lean_inc_ref_n(v_inst_3249_, 7);
v___f_3259_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3259_, 0, v_inst_3249_);
v___f_3260_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3260_, 0, v_inst_3249_);
v___f_3261_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3261_, 0, v_inst_3249_);
v___f_3262_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3262_, 0, v_inst_3249_);
v___f_3263_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3263_, 0, v_inst_3249_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___f_3259_);
lean_ctor_set(v___x_3264_, 1, v___f_3260_);
v___x_3265_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3265_, 0, lean_box(0));
lean_closure_set(v___x_3265_, 1, v_inst_3249_);
v___x_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
lean_ctor_set(v___x_3266_, 2, v___f_3261_);
lean_ctor_set(v___x_3266_, 3, v___f_3262_);
lean_ctor_set(v___x_3266_, 4, v___f_3263_);
v___x_3267_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3267_, 0, lean_box(0));
lean_closure_set(v___x_3267_, 1, v_inst_3249_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3278_ = l_Lean_Name_hasMacroScopes(v_n_3258_);
if (v___x_3278_ == 0)
{
lean_object* v_toApplicative_3279_; lean_object* v_toPure_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_toApplicative_3279_ = lean_ctor_get(v_inst_3249_, 0);
v_toPure_3280_ = lean_ctor_get(v_toApplicative_3279_, 1);
v___x_3281_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3280_);
v___x_3282_ = lean_apply_2(v_toPure_3280_, lean_box(0), v___x_3281_);
v___y_3270_ = v___x_3282_;
goto v___jp_3269_;
}
else
{
lean_object* v_toApplicative_3283_; lean_object* v_toPure_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_toApplicative_3283_ = lean_ctor_get(v_inst_3249_, 0);
v_toPure_3284_ = lean_ctor_get(v_toApplicative_3283_, 1);
v___x_3285_ = lean_box(0);
lean_inc(v_toPure_3284_);
v___x_3286_ = lean_apply_2(v_toPure_3284_, lean_box(0), v___x_3285_);
v___y_3270_ = v___x_3286_;
goto v___jp_3269_;
}
v___jp_3269_:
{
lean_object* v_toApplicative_3271_; lean_object* v_toBind_3272_; lean_object* v_toPure_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___f_3276_; lean_object* v___x_3277_; 
v_toApplicative_3271_ = lean_ctor_get(v_inst_3249_, 0);
v_toBind_3272_ = lean_ctor_get(v_inst_3249_, 1);
lean_inc_n(v_toBind_3272_, 2);
v_toPure_3273_ = lean_ctor_get(v_toApplicative_3271_, 1);
lean_inc_n(v_toPure_3273_, 3);
v___f_3274_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3274_, 0, v_toPure_3273_);
v___f_3275_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3275_, 0, v_toPure_3273_);
v___f_3276_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3276_, 0, v_toPure_3273_);
lean_closure_set(v___f_3276_, 1, v_n_3258_);
lean_closure_set(v___f_3276_, 2, v_inst_3249_);
lean_closure_set(v___f_3276_, 3, v_inst_3250_);
lean_closure_set(v___f_3276_, 4, v_inst_3251_);
lean_closure_set(v___f_3276_, 5, v_inst_3252_);
lean_closure_set(v___f_3276_, 6, v_inst_3253_);
lean_closure_set(v___f_3276_, 7, v_inst_3254_);
lean_closure_set(v___f_3276_, 8, v_n_u2080_3255_);
lean_closure_set(v___f_3276_, 9, v_filter_3256_);
lean_closure_set(v___f_3276_, 10, v_view_x3f_3257_);
lean_closure_set(v___f_3276_, 11, v_toBind_3272_);
lean_closure_set(v___f_3276_, 12, v___f_3275_);
lean_closure_set(v___f_3276_, 13, v___f_3274_);
lean_closure_set(v___f_3276_, 14, v___x_3268_);
v___x_3277_ = lean_apply_4(v_toBind_3272_, lean_box(0), lean_box(0), v___y_3270_, v___f_3276_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_inst_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_n_u2080_3294_, lean_object* v_filter_3295_, lean_object* v_view_x3f_3296_, lean_object* v_n_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3288_, v_inst_3289_, v_inst_3290_, v_inst_3291_, v_inst_3292_, v_inst_3293_, v_n_u2080_3294_, v_filter_3295_, v_view_x3f_3296_, v_n_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3299_, lean_object* v_x1_3300_, lean_object* v_x2_3301_){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3302_ = l_Lean_Name_getPrefix(v_x2_3301_);
v___x_3303_ = l_Lean_Name_getPrefix(v_n_u2081_3299_);
v___x_3304_ = l_Lean_Name_isPrefixOf(v___x_3302_, v___x_3303_);
lean_dec(v___x_3303_);
lean_dec(v___x_3302_);
if (v___x_3304_ == 0)
{
lean_dec(v_x2_3301_);
return v_x1_3300_;
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_array_push(v_x1_3300_, v_x2_3301_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3306_, lean_object* v_x1_3307_, lean_object* v_x2_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3306_, v_x1_3307_, v_x2_3308_);
lean_dec(v_n_u2081_3306_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3310_, lean_object* v_n_u2081_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_n_u2080_3318_, lean_object* v_filter_3319_, lean_object* v_toPure_3320_, lean_object* v_____do__lift_3321_){
_start:
{
if (lean_obj_tag(v_____do__lift_3321_) == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec(v_toPure_3320_);
v___x_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_view_3310_);
v___x_3323_ = l_Lean_rootNamespace;
v___x_3324_ = l_Lean_Name_append(v___x_3323_, v_n_u2081_3311_);
v___x_3325_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3312_, v_inst_3313_, v_inst_3314_, v_inst_3315_, v_inst_3316_, v_inst_3317_, v_n_u2080_3318_, v_filter_3319_, v___x_3322_, v___x_3324_);
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; 
lean_dec(v_filter_3319_);
lean_dec(v_n_u2080_3318_);
lean_dec(v_inst_3317_);
lean_dec_ref(v_inst_3316_);
lean_dec(v_inst_3315_);
lean_dec_ref(v_inst_3314_);
lean_dec_ref(v_inst_3313_);
lean_dec_ref(v_inst_3312_);
lean_dec(v_n_u2081_3311_);
lean_dec_ref(v_view_3310_);
v___x_3326_ = lean_apply_2(v_toPure_3320_, lean_box(0), v_____do__lift_3321_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_n_u2080_3334_, lean_object* v_filter_3335_, lean_object* v___x_3336_, lean_object* v_toBind_3337_, lean_object* v___f_3338_, uint8_t v_allowHorizAliases_3339_, lean_object* v___f_3340_, lean_object* v_____do__lift_3341_){
_start:
{
lean_object* v_aliases_3343_; 
if (lean_obj_tag(v_____do__lift_3341_) == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec_ref(v___f_3340_);
lean_dec(v___f_3338_);
lean_dec(v_toBind_3337_);
lean_dec_ref(v___x_3336_);
lean_dec(v_filter_3335_);
lean_dec(v_n_u2080_3334_);
lean_dec(v_inst_3333_);
lean_dec_ref(v_inst_3332_);
lean_dec(v_inst_3331_);
lean_dec_ref(v_inst_3330_);
lean_dec_ref(v_inst_3329_);
lean_dec_ref(v_inst_3328_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_apply_2(v_toPure_3327_, lean_box(0), v___x_3349_);
return v___x_3350_;
}
else
{
lean_object* v_val_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec(v_toPure_3327_);
v_val_3351_ = lean_ctor_get(v_____do__lift_3341_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v_____do__lift_3341_, 1);
lean_inc(v_n_u2080_3334_);
v___x_3352_ = l_Lean_getRevAliases(v_val_3351_, v_n_u2080_3334_);
v___x_3353_ = lean_array_mk(v___x_3352_);
if (v_allowHorizAliases_3339_ == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3354_ = lean_unsigned_to_nat(0u);
v___x_3355_ = lean_array_get_size(v___x_3353_);
v___x_3356_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3357_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3358_ = lean_nat_dec_lt(v___x_3354_, v___x_3355_);
if (v___x_3358_ == 0)
{
lean_dec_ref(v___x_3353_);
lean_dec_ref(v___f_3340_);
v_aliases_3343_ = v___x_3356_;
goto v___jp_3342_;
}
else
{
uint8_t v___x_3359_; 
v___x_3359_ = lean_nat_dec_le(v___x_3355_, v___x_3355_);
if (v___x_3359_ == 0)
{
if (v___x_3358_ == 0)
{
lean_dec_ref(v___x_3353_);
lean_dec_ref(v___f_3340_);
v_aliases_3343_ = v___x_3356_;
goto v___jp_3342_;
}
else
{
size_t v___x_3360_; size_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = lean_usize_of_nat(v___x_3355_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3357_, v___f_3340_, v___x_3353_, v___x_3360_, v___x_3361_, v___x_3356_);
v_aliases_3343_ = v___x_3362_;
goto v___jp_3342_;
}
}
else
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = lean_usize_of_nat(v___x_3355_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3357_, v___f_3340_, v___x_3353_, v___x_3363_, v___x_3364_, v___x_3356_);
v_aliases_3343_ = v___x_3365_;
goto v___jp_3342_;
}
}
}
else
{
lean_dec_ref(v___f_3340_);
v_aliases_3343_ = v___x_3353_;
goto v___jp_3342_;
}
}
v___jp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3345_, 0, lean_box(0));
lean_closure_set(v___x_3345_, 1, v_inst_3328_);
lean_closure_set(v___x_3345_, 2, v_inst_3329_);
lean_closure_set(v___x_3345_, 3, v_inst_3330_);
lean_closure_set(v___x_3345_, 4, v_inst_3331_);
lean_closure_set(v___x_3345_, 5, v_inst_3332_);
lean_closure_set(v___x_3345_, 6, v_inst_3333_);
lean_closure_set(v___x_3345_, 7, v_n_u2080_3334_);
lean_closure_set(v___x_3345_, 8, v_filter_3335_);
lean_closure_set(v___x_3345_, 9, v___x_3344_);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3336_, v___x_3345_, v_aliases_3343_, v___x_3346_);
v___x_3348_ = lean_apply_4(v_toBind_3337_, lean_box(0), lean_box(0), v___x_3347_, v___f_3338_);
return v___x_3348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_inst_3372_, lean_object* v_n_u2080_3373_, lean_object* v_filter_3374_, lean_object* v___x_3375_, lean_object* v_toBind_3376_, lean_object* v___f_3377_, lean_object* v_allowHorizAliases_3378_, lean_object* v___f_3379_, lean_object* v_____do__lift_3380_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3381_; lean_object* v_res_3382_; 
v_allowHorizAliases_boxed_3381_ = lean_unbox(v_allowHorizAliases_3378_);
v_res_3382_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3366_, v_inst_3367_, v_inst_3368_, v_inst_3369_, v_inst_3370_, v_inst_3371_, v_inst_3372_, v_n_u2080_3373_, v_filter_3374_, v___x_3375_, v_toBind_3376_, v___f_3377_, v_allowHorizAliases_boxed_3381_, v___f_3379_, v_____do__lift_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3383_, lean_object* v_____do__lift_3384_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_____do__lift_3384_);
v___x_3386_ = lean_apply_2(v_toPure_3383_, lean_box(0), v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3387_, lean_object* v_inst_3388_, lean_object* v_inst_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_n_u2080_3394_, lean_object* v_filter_3395_, lean_object* v___x_3396_, lean_object* v_toPure_3397_, lean_object* v_____do__lift_3398_){
_start:
{
if (lean_obj_tag(v_____do__lift_3398_) == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
lean_dec(v_toPure_3397_);
v___x_3399_ = l_Lean_rootNamespace;
v___x_3400_ = l_Lean_Name_append(v___x_3399_, v_n_u2081_3387_);
v___x_3401_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3388_, v_inst_3389_, v_inst_3390_, v_inst_3391_, v_inst_3392_, v_inst_3393_, v_n_u2080_3394_, v_filter_3395_, v___x_3396_, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; 
lean_dec(v___x_3396_);
lean_dec(v_filter_3395_);
lean_dec(v_n_u2080_3394_);
lean_dec(v_inst_3393_);
lean_dec_ref(v_inst_3392_);
lean_dec(v_inst_3391_);
lean_dec_ref(v_inst_3390_);
lean_dec_ref(v_inst_3389_);
lean_dec_ref(v_inst_3388_);
lean_dec(v_n_u2081_3387_);
v___x_3402_ = lean_apply_2(v_toPure_3397_, lean_box(0), v_____do__lift_3398_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_n_u2080_3409_, uint8_t v_fullNames_3410_, uint8_t v_allowHorizAliases_3411_, lean_object* v_filter_3412_){
_start:
{
lean_object* v_view_3413_; lean_object* v_name_3414_; lean_object* v_n_u2081_3415_; lean_object* v___x_3416_; 
lean_inc(v_n_u2080_3409_);
v_view_3413_ = l_Lean_extractMacroScopes(v_n_u2080_3409_);
v_name_3414_ = lean_ctor_get(v_view_3413_, 0);
lean_inc(v_name_3414_);
v_n_u2081_3415_ = l_Lean_privateToUserName(v_name_3414_);
lean_inc_ref(v_inst_3403_);
v___x_3416_ = l_OptionT_instAlternative___redArg(v_inst_3403_);
if (v_fullNames_3410_ == 0)
{
lean_object* v_toApplicative_3417_; lean_object* v_getEnv_3418_; lean_object* v_toBind_3419_; lean_object* v_toPure_3420_; lean_object* v___f_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___f_3424_; lean_object* v___f_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_toApplicative_3417_ = lean_ctor_get(v_inst_3403_, 0);
v_getEnv_3418_ = lean_ctor_get(v_inst_3405_, 0);
lean_inc(v_getEnv_3418_);
v_toBind_3419_ = lean_ctor_get(v_inst_3403_, 1);
lean_inc_n(v_toBind_3419_, 3);
v_toPure_3420_ = lean_ctor_get(v_toApplicative_3417_, 1);
lean_inc_n(v_toPure_3420_, 3);
lean_inc(v_n_u2081_3415_);
v___f_3421_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3421_, 0, v_n_u2081_3415_);
lean_inc(v_filter_3412_);
lean_inc(v_n_u2080_3409_);
lean_inc(v_inst_3408_);
lean_inc_ref(v_inst_3407_);
lean_inc(v_inst_3406_);
lean_inc_ref(v_inst_3405_);
lean_inc_ref(v_inst_3404_);
lean_inc_ref(v_inst_3403_);
v___f_3422_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3422_, 0, v_view_3413_);
lean_closure_set(v___f_3422_, 1, v_n_u2081_3415_);
lean_closure_set(v___f_3422_, 2, v_inst_3403_);
lean_closure_set(v___f_3422_, 3, v_inst_3404_);
lean_closure_set(v___f_3422_, 4, v_inst_3405_);
lean_closure_set(v___f_3422_, 5, v_inst_3406_);
lean_closure_set(v___f_3422_, 6, v_inst_3407_);
lean_closure_set(v___f_3422_, 7, v_inst_3408_);
lean_closure_set(v___f_3422_, 8, v_n_u2080_3409_);
lean_closure_set(v___f_3422_, 9, v_filter_3412_);
lean_closure_set(v___f_3422_, 10, v_toPure_3420_);
v___x_3423_ = lean_box(v_allowHorizAliases_3411_);
v___f_3424_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_3424_, 0, v_toPure_3420_);
lean_closure_set(v___f_3424_, 1, v_inst_3403_);
lean_closure_set(v___f_3424_, 2, v_inst_3404_);
lean_closure_set(v___f_3424_, 3, v_inst_3405_);
lean_closure_set(v___f_3424_, 4, v_inst_3406_);
lean_closure_set(v___f_3424_, 5, v_inst_3407_);
lean_closure_set(v___f_3424_, 6, v_inst_3408_);
lean_closure_set(v___f_3424_, 7, v_n_u2080_3409_);
lean_closure_set(v___f_3424_, 8, v_filter_3412_);
lean_closure_set(v___f_3424_, 9, v___x_3416_);
lean_closure_set(v___f_3424_, 10, v_toBind_3419_);
lean_closure_set(v___f_3424_, 11, v___f_3422_);
lean_closure_set(v___f_3424_, 12, v___x_3423_);
lean_closure_set(v___f_3424_, 13, v___f_3421_);
v___f_3425_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3425_, 0, v_toPure_3420_);
v___x_3426_ = lean_apply_4(v_toBind_3419_, lean_box(0), lean_box(0), v_getEnv_3418_, v___f_3425_);
v___x_3427_ = lean_apply_4(v_toBind_3419_, lean_box(0), lean_box(0), v___x_3426_, v___f_3424_);
return v___x_3427_;
}
else
{
lean_object* v_toApplicative_3428_; lean_object* v_toBind_3429_; lean_object* v_toPure_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; 
lean_dec_ref(v___x_3416_);
v_toApplicative_3428_ = lean_ctor_get(v_inst_3403_, 0);
v_toBind_3429_ = lean_ctor_get(v_inst_3403_, 1);
lean_inc(v_toBind_3429_);
v_toPure_3430_ = lean_ctor_get(v_toApplicative_3428_, 1);
lean_inc(v_toPure_3430_);
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v_view_3413_);
lean_inc(v_n_u2081_3415_);
lean_inc_ref(v___x_3431_);
lean_inc(v_filter_3412_);
lean_inc(v_n_u2080_3409_);
lean_inc(v_inst_3408_);
lean_inc_ref(v_inst_3407_);
lean_inc(v_inst_3406_);
lean_inc_ref(v_inst_3405_);
lean_inc_ref(v_inst_3404_);
lean_inc_ref(v_inst_3403_);
v___x_3432_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_inst_3407_, v_inst_3408_, v_n_u2080_3409_, v_filter_3412_, v___x_3431_, v_n_u2081_3415_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3433_, 0, v_n_u2081_3415_);
lean_closure_set(v___f_3433_, 1, v_inst_3403_);
lean_closure_set(v___f_3433_, 2, v_inst_3404_);
lean_closure_set(v___f_3433_, 3, v_inst_3405_);
lean_closure_set(v___f_3433_, 4, v_inst_3406_);
lean_closure_set(v___f_3433_, 5, v_inst_3407_);
lean_closure_set(v___f_3433_, 6, v_inst_3408_);
lean_closure_set(v___f_3433_, 7, v_n_u2080_3409_);
lean_closure_set(v___f_3433_, 8, v_filter_3412_);
lean_closure_set(v___f_3433_, 9, v___x_3431_);
lean_closure_set(v___f_3433_, 10, v_toPure_3430_);
v___x_3434_ = lean_apply_4(v_toBind_3429_, lean_box(0), lean_box(0), v___x_3432_, v___f_3433_);
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3435_, lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_n_u2080_3441_, lean_object* v_fullNames_3442_, lean_object* v_allowHorizAliases_3443_, lean_object* v_filter_3444_){
_start:
{
uint8_t v_fullNames_boxed_3445_; uint8_t v_allowHorizAliases_boxed_3446_; lean_object* v_res_3447_; 
v_fullNames_boxed_3445_ = lean_unbox(v_fullNames_3442_);
v_allowHorizAliases_boxed_3446_ = lean_unbox(v_allowHorizAliases_3443_);
v_res_3447_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3435_, v_inst_3436_, v_inst_3437_, v_inst_3438_, v_inst_3439_, v_inst_3440_, v_n_u2080_3441_, v_fullNames_boxed_3445_, v_allowHorizAliases_boxed_3446_, v_filter_3444_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_n_u2080_3455_, uint8_t v_fullNames_3456_, uint8_t v_allowHorizAliases_3457_, lean_object* v_filter_3458_){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3449_, v_inst_3450_, v_inst_3451_, v_inst_3452_, v_inst_3453_, v_inst_3454_, v_n_u2080_3455_, v_fullNames_3456_, v_allowHorizAliases_3457_, v_filter_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_inst_3466_, lean_object* v_n_u2080_3467_, lean_object* v_fullNames_3468_, lean_object* v_allowHorizAliases_3469_, lean_object* v_filter_3470_){
_start:
{
uint8_t v_fullNames_boxed_3471_; uint8_t v_allowHorizAliases_boxed_3472_; lean_object* v_res_3473_; 
v_fullNames_boxed_3471_ = lean_unbox(v_fullNames_3468_);
v_allowHorizAliases_boxed_3472_ = lean_unbox(v_allowHorizAliases_3469_);
v_res_3473_ = l_Lean_unresolveNameGlobal_x3f(v_m_3460_, v_inst_3461_, v_inst_3462_, v_inst_3463_, v_inst_3464_, v_inst_3465_, v_inst_3466_, v_n_u2080_3467_, v_fullNames_boxed_3471_, v_allowHorizAliases_boxed_3472_, v_filter_3470_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3474_, lean_object* v_n_u2080_3475_, lean_object* v_n_x3f_3476_){
_start:
{
if (lean_obj_tag(v_n_x3f_3476_) == 0)
{
lean_object* v___x_3477_; 
v___x_3477_ = lean_apply_2(v_toPure_3474_, lean_box(0), v_n_u2080_3475_);
return v___x_3477_;
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3479_; 
lean_dec(v_n_u2080_3475_);
v_val_3478_ = lean_ctor_get(v_n_x3f_3476_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v_n_x3f_3476_, 1);
v___x_3479_ = lean_apply_2(v_toPure_3474_, lean_box(0), v_val_3478_);
return v___x_3479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_n_u2080_3486_, uint8_t v_fullNames_3487_, uint8_t v_allowHorizAliases_3488_, lean_object* v_filter_3489_){
_start:
{
lean_object* v_toApplicative_3490_; lean_object* v_toBind_3491_; lean_object* v_toPure_3492_; lean_object* v___x_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; 
v_toApplicative_3490_ = lean_ctor_get(v_inst_3480_, 0);
v_toBind_3491_ = lean_ctor_get(v_inst_3480_, 1);
lean_inc(v_toBind_3491_);
v_toPure_3492_ = lean_ctor_get(v_toApplicative_3490_, 1);
lean_inc(v_toPure_3492_);
lean_inc(v_n_u2080_3486_);
v___x_3493_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3480_, v_inst_3481_, v_inst_3482_, v_inst_3483_, v_inst_3484_, v_inst_3485_, v_n_u2080_3486_, v_fullNames_3487_, v_allowHorizAliases_3488_, v_filter_3489_);
v___f_3494_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3494_, 0, v_toPure_3492_);
lean_closure_set(v___f_3494_, 1, v_n_u2080_3486_);
v___x_3495_ = lean_apply_4(v_toBind_3491_, lean_box(0), lean_box(0), v___x_3493_, v___f_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_, lean_object* v_inst_3501_, lean_object* v_n_u2080_3502_, lean_object* v_fullNames_3503_, lean_object* v_allowHorizAliases_3504_, lean_object* v_filter_3505_){
_start:
{
uint8_t v_fullNames_boxed_3506_; uint8_t v_allowHorizAliases_boxed_3507_; lean_object* v_res_3508_; 
v_fullNames_boxed_3506_ = lean_unbox(v_fullNames_3503_);
v_allowHorizAliases_boxed_3507_ = lean_unbox(v_allowHorizAliases_3504_);
v_res_3508_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3496_, v_inst_3497_, v_inst_3498_, v_inst_3499_, v_inst_3500_, v_inst_3501_, v_n_u2080_3502_, v_fullNames_boxed_3506_, v_allowHorizAliases_boxed_3507_, v_filter_3505_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_inst_3515_, lean_object* v_n_u2080_3516_, uint8_t v_fullNames_3517_, uint8_t v_allowHorizAliases_3518_, lean_object* v_filter_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_inst_3514_, v_inst_3515_, v_n_u2080_3516_, v_fullNames_3517_, v_allowHorizAliases_3518_, v_filter_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_n_u2080_3528_, lean_object* v_fullNames_3529_, lean_object* v_allowHorizAliases_3530_, lean_object* v_filter_3531_){
_start:
{
uint8_t v_fullNames_boxed_3532_; uint8_t v_allowHorizAliases_boxed_3533_; lean_object* v_res_3534_; 
v_fullNames_boxed_3532_ = lean_unbox(v_fullNames_3529_);
v_allowHorizAliases_boxed_3533_ = lean_unbox(v_allowHorizAliases_3530_);
v_res_3534_ = l_Lean_unresolveNameGlobal(v_m_3521_, v_inst_3522_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v_inst_3526_, v_inst_3527_, v_n_u2080_3528_, v_fullNames_boxed_3532_, v_allowHorizAliases_boxed_3533_, v_filter_3531_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_inst_3543_, lean_object* v_n_3544_){
_start:
{
lean_object* v_map_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_map_3545_ = lean_ctor_get(v_toFunctor_3536_, 0);
lean_inc(v_map_3545_);
lean_dec_ref(v_toFunctor_3536_);
v___x_3546_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3547_ = l_Lean_resolveLocalName___redArg(v_inst_3537_, v_inst_3538_, v_inst_3539_, v_inst_3540_, v_inst_3541_, v_inst_3542_, v_inst_3543_, v_n_3544_);
v___x_3548_ = lean_apply_4(v_map_3545_, lean_box(0), lean_box(0), v___x_3546_, v___x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_n_u2080_3556_, uint8_t v_fullNames_3557_){
_start:
{
lean_object* v_toApplicative_3558_; lean_object* v_toFunctor_3559_; uint8_t v___x_3560_; lean_object* v___f_3561_; lean_object* v___x_3562_; 
v_toApplicative_3558_ = lean_ctor_get(v_inst_3549_, 0);
v_toFunctor_3559_ = lean_ctor_get(v_toApplicative_3558_, 0);
v___x_3560_ = 0;
lean_inc(v_inst_3554_);
lean_inc_ref(v_inst_3553_);
lean_inc(v_inst_3552_);
lean_inc_ref(v_inst_3551_);
lean_inc_ref(v_inst_3550_);
lean_inc_ref(v_inst_3549_);
lean_inc_ref(v_toFunctor_3559_);
v___f_3561_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3561_, 0, v_toFunctor_3559_);
lean_closure_set(v___f_3561_, 1, v_inst_3549_);
lean_closure_set(v___f_3561_, 2, v_inst_3550_);
lean_closure_set(v___f_3561_, 3, v_inst_3551_);
lean_closure_set(v___f_3561_, 4, v_inst_3552_);
lean_closure_set(v___f_3561_, 5, v_inst_3553_);
lean_closure_set(v___f_3561_, 6, v_inst_3554_);
lean_closure_set(v___f_3561_, 7, v_inst_3555_);
v___x_3562_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3549_, v_inst_3550_, v_inst_3551_, v_inst_3552_, v_inst_3553_, v_inst_3554_, v_n_u2080_3556_, v_fullNames_3557_, v___x_3560_, v___f_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_n_u2080_3570_, lean_object* v_fullNames_3571_){
_start:
{
uint8_t v_fullNames_boxed_3572_; lean_object* v_res_3573_; 
v_fullNames_boxed_3572_ = lean_unbox(v_fullNames_3571_);
v_res_3573_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3563_, v_inst_3564_, v_inst_3565_, v_inst_3566_, v_inst_3567_, v_inst_3568_, v_inst_3569_, v_n_u2080_3570_, v_fullNames_boxed_3572_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_inst_3581_, lean_object* v_n_u2080_3582_, uint8_t v_fullNames_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3575_, v_inst_3576_, v_inst_3577_, v_inst_3578_, v_inst_3579_, v_inst_3580_, v_inst_3581_, v_n_u2080_3582_, v_fullNames_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_n_u2080_3593_, lean_object* v_fullNames_3594_){
_start:
{
uint8_t v_fullNames_boxed_3595_; lean_object* v_res_3596_; 
v_fullNames_boxed_3595_ = lean_unbox(v_fullNames_3594_);
v_res_3596_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3585_, v_inst_3586_, v_inst_3587_, v_inst_3588_, v_inst_3589_, v_inst_3590_, v_inst_3591_, v_inst_3592_, v_n_u2080_3593_, v_fullNames_boxed_3595_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_n_u2080_3604_, uint8_t v_fullNames_3605_){
_start:
{
lean_object* v_toApplicative_3606_; lean_object* v_toBind_3607_; lean_object* v_toPure_3608_; lean_object* v___x_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; 
v_toApplicative_3606_ = lean_ctor_get(v_inst_3597_, 0);
v_toBind_3607_ = lean_ctor_get(v_inst_3597_, 1);
lean_inc(v_toBind_3607_);
v_toPure_3608_ = lean_ctor_get(v_toApplicative_3606_, 1);
lean_inc(v_toPure_3608_);
lean_inc(v_n_u2080_3604_);
v___x_3609_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_inst_3602_, v_inst_3603_, v_n_u2080_3604_, v_fullNames_3605_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3610_, 0, v_toPure_3608_);
lean_closure_set(v___f_3610_, 1, v_n_u2080_3604_);
v___x_3611_ = lean_apply_4(v_toBind_3607_, lean_box(0), lean_box(0), v___x_3609_, v___f_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_inst_3618_, lean_object* v_n_u2080_3619_, lean_object* v_fullNames_3620_){
_start:
{
uint8_t v_fullNames_boxed_3621_; lean_object* v_res_3622_; 
v_fullNames_boxed_3621_ = lean_unbox(v_fullNames_3620_);
v_res_3622_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_inst_3618_, v_n_u2080_3619_, v_fullNames_boxed_3621_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3623_, lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_n_u2080_3631_, uint8_t v_fullNames_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_inst_3630_, v_n_u2080_3631_, v_fullNames_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3634_, lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_n_u2080_3642_, lean_object* v_fullNames_3643_){
_start:
{
uint8_t v_fullNames_boxed_3644_; lean_object* v_res_3645_; 
v_fullNames_boxed_3644_ = lean_unbox(v_fullNames_3643_);
v_res_3645_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3634_, v_inst_3635_, v_inst_3636_, v_inst_3637_, v_inst_3638_, v_inst_3639_, v_inst_3640_, v_inst_3641_, v_n_u2080_3642_, v_fullNames_boxed_3644_);
return v_res_3645_;
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
