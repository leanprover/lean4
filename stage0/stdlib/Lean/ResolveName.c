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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SMap_instInhabited___redArg();
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_instInhabited___redArg();
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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_getAliasState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAliasState___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; 
v___f_96_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_box(2);
v___x_99_ = lean_box(0);
v___x_100_ = 0;
v___x_101_ = l_Lean_registerEnvExtension___redArg(v___f_96_, v___x_97_, v___x_98_, v___x_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_env_104_, lean_object* v_name_105_, lean_object* v_as_106_, size_t v_i_107_, size_t v_stop_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_usize_dec_eq(v_i_107_, v_stop_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_153__overap_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_153__overap_110_ = lean_array_uget_borrowed(v_as_106_, v_i_107_);
lean_inc(v___x_153__overap_110_);
lean_inc(v_name_105_);
lean_inc_ref(v_env_104_);
v___x_111_ = lean_apply_2(v___x_153__overap_110_, v_env_104_, v_name_105_);
v___x_112_ = lean_unbox(v___x_111_);
if (v___x_112_ == 0)
{
size_t v___x_113_; size_t v___x_114_; 
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_107_, v___x_113_);
v_i_107_ = v___x_114_;
goto _start;
}
else
{
uint8_t v___x_116_; 
lean_dec(v_name_105_);
lean_dec_ref(v_env_104_);
v___x_116_ = lean_unbox(v___x_111_);
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
lean_dec(v_name_105_);
lean_dec_ref(v_env_104_);
v___x_117_ = 0;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_env_118_, lean_object* v_name_119_, lean_object* v_as_120_, lean_object* v_i_121_, lean_object* v_stop_122_){
_start:
{
size_t v_i_boxed_123_; size_t v_stop_boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_i_boxed_123_ = lean_unbox_usize(v_i_121_);
lean_dec(v_i_121_);
v_stop_boxed_124_ = lean_unbox_usize(v_stop_122_);
lean_dec(v_stop_122_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_118_, v_name_119_, v_as_120_, v_i_boxed_123_, v_stop_boxed_124_);
lean_dec_ref(v_as_120_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Array_instInhabited___redArg();
return v___x_127_;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* v_env_128_, lean_object* v_name_129_){
_start:
{
lean_object* v___x_130_; lean_object* v_asyncMode_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_130_ = l_Lean_reservedNamePredicatesExt;
v_asyncMode_131_ = lean_ctor_get(v___x_130_, 2);
v___x_132_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_133_ = lean_box(0);
lean_inc_ref(v_env_128_);
v___x_134_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_132_, v___x_130_, v_env_128_, v_asyncMode_131_, v___x_133_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v___x_134_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec(v___x_134_);
lean_dec(v_name_129_);
lean_dec_ref(v_env_128_);
return v___x_137_;
}
else
{
if (v___x_137_ == 0)
{
lean_dec(v___x_134_);
lean_dec(v_name_129_);
lean_dec_ref(v_env_128_);
return v___x_137_;
}
else
{
size_t v___x_138_; size_t v___x_139_; uint8_t v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_136_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_128_, v_name_129_, v___x_134_, v___x_138_, v___x_139_);
lean_dec(v___x_134_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_141_, lean_object* v_name_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = lean_is_reserved_name(v_env_141_, v_name_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_ks_149_; lean_object* v_vs_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_174_; 
v_ks_149_ = lean_ctor_get(v_x_145_, 0);
v_vs_150_ = lean_ctor_get(v_x_145_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_174_ == 0)
{
v___x_152_ = v_x_145_;
v_isShared_153_ = v_isSharedCheck_174_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_vs_150_);
lean_inc(v_ks_149_);
lean_dec(v_x_145_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_174_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_array_get_size(v_ks_149_);
v___x_155_ = lean_nat_dec_lt(v_x_146_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
lean_dec(v_x_146_);
v___x_156_ = lean_array_push(v_ks_149_, v_x_147_);
v___x_157_ = lean_array_push(v_vs_150_, v_x_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_157_);
lean_ctor_set(v___x_152_, 0, v___x_156_);
v___x_159_ = v___x_152_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v_k_x27_161_; uint8_t v___x_162_; 
v_k_x27_161_ = lean_array_fget_borrowed(v_ks_149_, v_x_146_);
v___x_162_ = lean_name_eq(v_x_147_, v_k_x27_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_164_; 
if (v_isShared_153_ == 0)
{
v___x_164_ = v___x_152_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_ks_149_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_vs_150_);
v___x_164_ = v_reuseFailAlloc_168_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_x_146_, v___x_165_);
lean_dec(v_x_146_);
v_x_145_ = v___x_164_;
v_x_146_ = v___x_166_;
goto _start;
}
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_169_ = lean_array_fset(v_ks_149_, v_x_146_, v_x_147_);
v___x_170_ = lean_array_fset(v_vs_150_, v_x_146_, v_x_148_);
lean_dec(v_x_146_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_170_);
lean_ctor_set(v___x_152_, 0, v___x_169_);
v___x_172_ = v___x_152_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_175_, lean_object* v_k_176_, lean_object* v_v_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_175_, v___x_178_, v_k_176_, v_v_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* v_ks_232_; lean_object* v_vs_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_251_; 
v_ks_232_ = lean_ctor_get(v_x_181_, 0);
v_vs_233_ = lean_ctor_get(v_x_181_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_251_ == 0)
{
v___x_235_ = v_x_181_;
v_isShared_236_ = v_isSharedCheck_251_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_vs_233_);
lean_inc(v_ks_232_);
lean_dec(v_x_181_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_251_;
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
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_ks_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_vs_233_);
v___x_238_ = v_reuseFailAlloc_250_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v_newNode_239_; size_t v___x_240_; uint8_t v___x_241_; 
v_newNode_239_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_238_, v_x_184_, v_x_185_);
v___x_240_ = ((size_t)7ULL);
v___x_241_ = lean_usize_dec_le(v___x_240_, v_x_183_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_239_);
v___x_243_ = lean_unsigned_to_nat(4u);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
lean_dec(v___x_242_);
if (v___x_244_ == 0)
{
lean_object* v_ks_245_; lean_object* v_vs_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_ks_245_ = lean_ctor_get(v_newNode_239_, 0);
lean_inc_ref(v_ks_245_);
v_vs_246_ = lean_ctor_get(v_newNode_239_, 1);
lean_inc_ref(v_vs_246_);
lean_dec_ref(v_newNode_239_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_183_, v_ks_245_, v_vs_246_, v___x_247_, v___x_248_);
lean_dec_ref(v_vs_246_);
lean_dec_ref(v_ks_245_);
return v___x_249_;
}
else
{
return v_newNode_239_;
}
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
size_t v_x_1075__boxed_287_; size_t v_x_1076__boxed_288_; lean_object* v_res_289_; 
v_x_1075__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_1076__boxed_288_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_282_, v_x_1075__boxed_287_, v_x_1076__boxed_288_, v_x_285_, v_x_286_);
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
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_nbuckets_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_344_ = lean_array_get_size(v_data_343_);
v___x_345_ = lean_unsigned_to_nat(2u);
v_nbuckets_346_ = lean_nat_mul(v___x_344_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_box(0);
v___x_349_ = lean_mk_array(v_nbuckets_346_, v___x_348_);
v___x_350_ = lean_array_propagate_mark(v_data_343_, v___x_349_);
v___x_351_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_347_, v_data_343_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_353_) == 0)
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
else
{
lean_object* v_key_355_; lean_object* v_tail_356_; uint8_t v___x_357_; 
v_key_355_ = lean_ctor_get(v_x_353_, 0);
v_tail_356_ = lean_ctor_get(v_x_353_, 2);
v___x_357_ = lean_name_eq(v_key_355_, v_a_352_);
if (v___x_357_ == 0)
{
v_x_353_ = v_tail_356_;
goto _start;
}
else
{
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec(v_a_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_363_, lean_object* v_b_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_dec(v_b_364_);
lean_dec(v_a_363_);
return v_x_365_;
}
else
{
lean_object* v_key_366_; lean_object* v_value_367_; lean_object* v_tail_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_380_; 
v_key_366_ = lean_ctor_get(v_x_365_, 0);
v_value_367_ = lean_ctor_get(v_x_365_, 1);
v_tail_368_ = lean_ctor_get(v_x_365_, 2);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_365_);
if (v_isSharedCheck_380_ == 0)
{
v___x_370_ = v_x_365_;
v_isShared_371_ = v_isSharedCheck_380_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_tail_368_);
lean_inc(v_value_367_);
lean_inc(v_key_366_);
lean_dec(v_x_365_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_380_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_name_eq(v_key_366_, v_a_363_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_363_, v_b_364_, v_tail_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 2, v___x_373_);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_key_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_value_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v_value_367_);
lean_dec(v_key_366_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_b_364_);
lean_ctor_set(v___x_370_, 0, v_a_363_);
v___x_378_ = v___x_370_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_363_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_b_364_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_tail_368_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_381_, lean_object* v_a_382_, lean_object* v_b_383_){
_start:
{
lean_object* v_size_384_; lean_object* v_buckets_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_431_; 
v_size_384_ = lean_ctor_get(v_m_381_, 0);
v_buckets_385_ = lean_ctor_get(v_m_381_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_m_381_);
if (v_isSharedCheck_431_ == 0)
{
v___x_387_ = v_m_381_;
v_isShared_388_ = v_isSharedCheck_431_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_buckets_385_);
lean_inc(v_size_384_);
lean_dec(v_m_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_431_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; uint64_t v___y_391_; 
v___x_389_ = lean_array_get_size(v_buckets_385_);
if (lean_obj_tag(v_a_382_) == 0)
{
uint64_t v___x_429_; 
v___x_429_ = 1723ULL;
v___y_391_ = v___x_429_;
goto v___jp_390_;
}
else
{
uint64_t v_hash_430_; 
v_hash_430_ = lean_ctor_get_uint64(v_a_382_, sizeof(void*)*2);
v___y_391_ = v_hash_430_;
goto v___jp_390_;
}
v___jp_390_:
{
uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v_fold_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v_bkt_403_; uint8_t v___x_404_; 
v___x_392_ = 32ULL;
v___x_393_ = lean_uint64_shift_right(v___y_391_, v___x_392_);
v_fold_394_ = lean_uint64_xor(v___y_391_, v___x_393_);
v___x_395_ = 16ULL;
v___x_396_ = lean_uint64_shift_right(v_fold_394_, v___x_395_);
v___x_397_ = lean_uint64_xor(v_fold_394_, v___x_396_);
v___x_398_ = lean_uint64_to_usize(v___x_397_);
v___x_399_ = lean_usize_of_nat(v___x_389_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_sub(v___x_399_, v___x_400_);
v___x_402_ = lean_usize_land(v___x_398_, v___x_401_);
v_bkt_403_ = lean_array_uget_borrowed(v_buckets_385_, v___x_402_);
v___x_404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_382_, v_bkt_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v_size_x27_406_; lean_object* v___x_407_; lean_object* v_buckets_x27_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_405_ = lean_unsigned_to_nat(1u);
v_size_x27_406_ = lean_nat_add(v_size_384_, v___x_405_);
lean_dec(v_size_384_);
lean_inc(v_bkt_403_);
v___x_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_407_, 0, v_a_382_);
lean_ctor_set(v___x_407_, 1, v_b_383_);
lean_ctor_set(v___x_407_, 2, v_bkt_403_);
v_buckets_x27_408_ = lean_array_uset(v_buckets_385_, v___x_402_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(4u);
v___x_410_ = lean_nat_mul(v_size_x27_406_, v___x_409_);
v___x_411_ = lean_unsigned_to_nat(3u);
v___x_412_ = lean_nat_div(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_array_get_size(v_buckets_x27_408_);
v___x_414_ = lean_nat_dec_le(v___x_412_, v___x_413_);
lean_dec(v___x_412_);
if (v___x_414_ == 0)
{
lean_object* v_val_415_; lean_object* v___x_417_; 
v_val_415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_408_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_val_415_);
lean_ctor_set(v___x_387_, 0, v_size_x27_406_);
v___x_417_ = v___x_387_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_size_x27_406_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_val_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v___x_420_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_buckets_x27_408_);
lean_ctor_set(v___x_387_, 0, v_size_x27_406_);
v___x_420_ = v___x_387_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_size_x27_406_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_buckets_x27_408_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_object* v___x_422_; lean_object* v_buckets_x27_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_bkt_403_);
v___x_422_ = lean_box(0);
v_buckets_x27_423_ = lean_array_uset(v_buckets_385_, v___x_402_, v___x_422_);
v___x_424_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_382_, v_b_383_, v_bkt_403_);
v___x_425_ = lean_array_uset(v_buckets_x27_423_, v___x_402_, v___x_424_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_425_);
v___x_427_ = v___x_387_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_size_384_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_stage_u2081_435_; 
v_stage_u2081_435_ = lean_ctor_get_uint8(v_x_432_, sizeof(void*)*2);
if (v_stage_u2081_435_ == 0)
{
lean_object* v_map_u2081_436_; lean_object* v_map_u2082_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_map_u2081_436_ = lean_ctor_get(v_x_432_, 0);
v_map_u2082_437_ = lean_ctor_get(v_x_432_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v_x_432_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_map_u2082_437_);
lean_inc(v_map_u2081_436_);
lean_dec(v_x_432_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_437_, v_x_433_, v_x_434_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_map_u2081_436_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*2, v_stage_u2081_435_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_map_u2081_446_; lean_object* v_map_u2082_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_map_u2081_446_ = lean_ctor_get(v_x_432_, 0);
v_map_u2082_447_ = lean_ctor_get(v_x_432_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v_x_432_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_map_u2082_447_);
lean_inc(v_map_u2081_446_);
lean_dec(v_x_432_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_446_, v_x_433_, v_x_434_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_map_u2082_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*2, v_stage_u2081_435_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
lean_object* v_key_459_; lean_object* v_value_460_; lean_object* v_tail_461_; uint8_t v___x_462_; 
v_key_459_ = lean_ctor_get(v_x_457_, 0);
v_value_460_ = lean_ctor_get(v_x_457_, 1);
v_tail_461_ = lean_ctor_get(v_x_457_, 2);
v___x_462_ = lean_name_eq(v_key_459_, v_a_456_);
if (v___x_462_ == 0)
{
v_x_457_ = v_tail_461_;
goto _start;
}
else
{
lean_object* v___x_464_; 
lean_inc(v_value_460_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v_value_460_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_465_, v_x_466_);
lean_dec(v_x_466_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_buckets_470_; lean_object* v___x_471_; uint64_t v___y_473_; 
v_buckets_470_ = lean_ctor_get(v_m_468_, 1);
v___x_471_ = lean_array_get_size(v_buckets_470_);
if (lean_obj_tag(v_a_469_) == 0)
{
uint64_t v___x_487_; 
v___x_487_ = 1723ULL;
v___y_473_ = v___x_487_;
goto v___jp_472_;
}
else
{
uint64_t v_hash_488_; 
v_hash_488_ = lean_ctor_get_uint64(v_a_469_, sizeof(void*)*2);
v___y_473_ = v_hash_488_;
goto v___jp_472_;
}
v___jp_472_:
{
uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v_fold_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_474_ = 32ULL;
v___x_475_ = lean_uint64_shift_right(v___y_473_, v___x_474_);
v_fold_476_ = lean_uint64_xor(v___y_473_, v___x_475_);
v___x_477_ = 16ULL;
v___x_478_ = lean_uint64_shift_right(v_fold_476_, v___x_477_);
v___x_479_ = lean_uint64_xor(v_fold_476_, v___x_478_);
v___x_480_ = lean_uint64_to_usize(v___x_479_);
v___x_481_ = lean_usize_of_nat(v___x_471_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_sub(v___x_481_, v___x_482_);
v___x_484_ = lean_usize_land(v___x_480_, v___x_483_);
v___x_485_ = lean_array_uget_borrowed(v_buckets_470_, v___x_484_);
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_469_, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_m_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_array_get_size(v_keys_492_);
v___x_497_ = lean_nat_dec_lt(v_i_494_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v_i_494_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v_k_x27_499_; uint8_t v___x_500_; 
v_k_x27_499_ = lean_array_fget_borrowed(v_keys_492_, v_i_494_);
v___x_500_ = lean_name_eq(v_k_495_, v_k_x27_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_i_494_, v___x_501_);
lean_dec(v_i_494_);
v_i_494_ = v___x_502_;
goto _start;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_array_fget_borrowed(v_vals_493_, v_i_494_);
lean_dec(v_i_494_);
lean_inc(v___x_504_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_506_, lean_object* v_vals_507_, lean_object* v_i_508_, lean_object* v_k_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_506_, v_vals_507_, v_i_508_, v_k_509_);
lean_dec(v_k_509_);
lean_dec_ref(v_vals_507_);
lean_dec_ref(v_keys_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_511_, size_t v_x_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
lean_object* v_es_514_; lean_object* v___x_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v_j_518_; lean_object* v___x_519_; 
v_es_514_ = lean_ctor_get(v_x_511_, 0);
v___x_515_ = lean_box(2);
v___x_516_ = ((size_t)31ULL);
v___x_517_ = lean_usize_land(v_x_512_, v___x_516_);
v_j_518_ = lean_usize_to_nat(v___x_517_);
v___x_519_ = lean_array_get_borrowed(v___x_515_, v_es_514_, v_j_518_);
lean_dec(v_j_518_);
switch(lean_obj_tag(v___x_519_))
{
case 0:
{
lean_object* v_key_520_; lean_object* v_val_521_; uint8_t v___x_522_; 
v_key_520_ = lean_ctor_get(v___x_519_, 0);
v_val_521_ = lean_ctor_get(v___x_519_, 1);
v___x_522_ = lean_name_eq(v_x_513_, v_key_520_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_inc(v_val_521_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v_val_521_);
return v___x_524_;
}
}
case 1:
{
lean_object* v_node_525_; size_t v___x_526_; size_t v___x_527_; 
v_node_525_ = lean_ctor_get(v___x_519_, 0);
v___x_526_ = ((size_t)5ULL);
v___x_527_ = lean_usize_shift_right(v_x_512_, v___x_526_);
v_x_511_ = v_node_525_;
v_x_512_ = v___x_527_;
goto _start;
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = lean_box(0);
return v___x_529_;
}
}
}
else
{
lean_object* v_ks_530_; lean_object* v_vs_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_ks_530_ = lean_ctor_get(v_x_511_, 0);
v_vs_531_ = lean_ctor_get(v_x_511_, 1);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_530_, v_vs_531_, v___x_532_, v_x_513_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
size_t v_x_1579__boxed_537_; lean_object* v_res_538_; 
v_x_1579__boxed_537_ = lean_unbox_usize(v_x_535_);
lean_dec(v_x_535_);
v_res_538_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_534_, v_x_1579__boxed_537_, v_x_536_);
lean_dec(v_x_536_);
lean_dec_ref(v_x_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
uint64_t v___y_542_; 
if (lean_obj_tag(v_x_540_) == 0)
{
uint64_t v___x_545_; 
v___x_545_ = 1723ULL;
v___y_542_ = v___x_545_;
goto v___jp_541_;
}
else
{
uint64_t v_hash_546_; 
v_hash_546_ = lean_ctor_get_uint64(v_x_540_, sizeof(void*)*2);
v___y_542_ = v_hash_546_;
goto v___jp_541_;
}
v___jp_541_:
{
size_t v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_uint64_to_usize(v___y_542_);
v___x_544_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_539_, v___x_543_, v_x_540_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_547_, v_x_548_);
lean_dec(v_x_548_);
lean_dec_ref(v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
uint8_t v_stage_u2081_552_; 
v_stage_u2081_552_ = lean_ctor_get_uint8(v_x_550_, sizeof(void*)*2);
if (v_stage_u2081_552_ == 0)
{
lean_object* v_map_u2081_553_; lean_object* v_map_u2082_554_; lean_object* v___x_555_; 
v_map_u2081_553_ = lean_ctor_get(v_x_550_, 0);
v_map_u2082_554_ = lean_ctor_get(v_x_550_, 1);
v___x_555_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_554_, v_x_551_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_553_, v_x_551_);
return v___x_556_;
}
else
{
return v___x_555_;
}
}
else
{
lean_object* v_map_u2081_557_; lean_object* v___x_558_; 
v_map_u2081_557_ = lean_ctor_get(v_x_550_, 0);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_557_, v_x_551_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_559_, v_x_560_);
lean_dec(v_x_560_);
lean_dec_ref(v_x_559_);
return v_res_561_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_562_, lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
uint8_t v___x_564_; 
v___x_564_ = 0;
return v___x_564_;
}
else
{
lean_object* v_head_565_; lean_object* v_tail_566_; uint8_t v___x_567_; 
v_head_565_ = lean_ctor_get(v_x_563_, 0);
v_tail_566_ = lean_ctor_get(v_x_563_, 1);
v___x_567_ = lean_name_eq(v_a_562_, v_head_565_);
if (v___x_567_ == 0)
{
v_x_563_ = v_tail_566_;
goto _start;
}
else
{
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_569_, v_x_570_);
lean_dec(v_x_570_);
lean_dec(v_a_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_573_, lean_object* v_e_574_){
_start:
{
lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_592_; 
v_fst_575_ = lean_ctor_get(v_e_574_, 0);
v_snd_576_ = lean_ctor_get(v_e_574_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_e_574_);
if (v_isSharedCheck_592_ == 0)
{
v___x_578_ = v_e_574_;
v_isShared_579_ = v_isSharedCheck_592_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
lean_dec(v_e_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_592_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_573_, v_fst_575_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_box(0);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 1);
lean_ctor_set(v___x_578_, 1, v___x_581_);
lean_ctor_set(v___x_578_, 0, v_snd_576_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_snd_576_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_573_, v_fst_575_, v___x_583_);
return v___x_584_;
}
}
else
{
lean_object* v_val_586_; uint8_t v___x_587_; 
v_val_586_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v___x_580_, 1);
v___x_587_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_576_, v_val_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_589_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 1);
lean_ctor_set(v___x_578_, 1, v_val_586_);
lean_ctor_set(v___x_578_, 0, v_snd_576_);
v___x_589_ = v___x_578_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_snd_576_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_val_586_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_573_, v_fst_575_, v___x_589_);
return v___x_590_;
}
}
else
{
lean_dec(v_val_586_);
lean_del_object(v___x_578_);
lean_dec(v_snd_576_);
lean_dec(v_fst_575_);
return v_s_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_597_, v_x_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec_ref(v_x_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_602_, v_x_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_610_, v_x_611_, v_x_612_);
lean_dec(v_x_612_);
lean_dec_ref(v_x_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_615_, v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_618_, v_m_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_m_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_623_, v_x_624_, v_x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_627_, lean_object* v_m_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_628_, v_a_629_, v_b_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_1744__boxed_641_; lean_object* v_res_642_; 
v_x_1744__boxed_641_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_642_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_637_, v_x_638_, v_x_1744__boxed_641_, v_x_640_);
lean_dec(v_x_640_);
lean_dec_ref(v_x_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_643_, lean_object* v_a_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_647_, lean_object* v_a_648_, lean_object* v_x_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_647_, v_a_648_, v_x_649_);
lean_dec(v_x_649_);
lean_dec(v_a_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_651_, lean_object* v_x_652_, size_t v_x_653_, size_t v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_652_, v_x_653_, v_x_654_, v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
size_t v_x_1760__boxed_664_; size_t v_x_1761__boxed_665_; lean_object* v_res_666_; 
v_x_1760__boxed_664_ = lean_unbox_usize(v_x_660_);
lean_dec(v_x_660_);
v_x_1761__boxed_665_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_res_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_658_, v_x_659_, v_x_1760__boxed_664_, v_x_1761__boxed_665_, v_x_662_, v_x_663_);
return v_res_666_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_667_, lean_object* v_a_668_, lean_object* v_x_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_668_, v_x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_671_, lean_object* v_a_672_, lean_object* v_x_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_671_, v_a_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec(v_a_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_676_, lean_object* v_data_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_679_, lean_object* v_a_680_, lean_object* v_b_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_680_, v_b_681_, v_x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_684_, lean_object* v_keys_685_, lean_object* v_vals_686_, lean_object* v_heq_687_, lean_object* v_i_688_, lean_object* v_k_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_685_, v_vals_686_, v_i_688_, v_k_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_691_, lean_object* v_keys_692_, lean_object* v_vals_693_, lean_object* v_heq_694_, lean_object* v_i_695_, lean_object* v_k_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_691_, v_keys_692_, v_vals_693_, v_heq_694_, v_i_695_, v_k_696_);
lean_dec(v_k_696_);
lean_dec_ref(v_vals_693_);
lean_dec_ref(v_keys_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_698_, lean_object* v_n_699_, lean_object* v_k_700_, lean_object* v_v_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_699_, v_k_700_, v_v_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_703_, size_t v_depth_704_, lean_object* v_keys_705_, lean_object* v_vals_706_, lean_object* v_heq_707_, lean_object* v_i_708_, lean_object* v_entries_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_704_, v_keys_705_, v_vals_706_, v_i_708_, v_entries_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_711_, lean_object* v_depth_712_, lean_object* v_keys_713_, lean_object* v_vals_714_, lean_object* v_heq_715_, lean_object* v_i_716_, lean_object* v_entries_717_){
_start:
{
size_t v_depth_boxed_718_; lean_object* v_res_719_; 
v_depth_boxed_718_ = lean_unbox_usize(v_depth_712_);
lean_dec(v_depth_712_);
v_res_719_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_711_, v_depth_boxed_718_, v_keys_713_, v_vals_714_, v_heq_715_, v_i_716_, v_entries_717_);
lean_dec_ref(v_vals_714_);
lean_dec_ref(v_keys_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_720_, lean_object* v_i_721_, lean_object* v_source_722_, lean_object* v_target_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_721_, v_source_722_, v_target_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_725_, lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_726_, v_x_727_, v_x_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_735_){
_start:
{
uint8_t v_stage_u2081_736_; 
v_stage_u2081_736_ = lean_ctor_get_uint8(v_m_735_, sizeof(void*)*2);
if (v_stage_u2081_736_ == 0)
{
return v_m_735_;
}
else
{
lean_object* v_map_u2081_737_; lean_object* v_map_u2082_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
v_map_u2081_737_ = lean_ctor_get(v_m_735_, 0);
v_map_u2082_738_ = lean_ctor_get(v_m_735_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_m_735_);
if (v_isSharedCheck_746_ == 0)
{
v___x_740_ = v_m_735_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_map_u2082_738_);
lean_inc(v_map_u2081_737_);
lean_dec(v_m_735_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v___x_742_; lean_object* v___x_744_; 
v___x_742_ = 0;
if (v_isShared_741_ == 0)
{
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_map_u2081_737_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_map_u2082_738_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*2, v___x_742_);
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_747_, lean_object* v_m_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_array_mk(v_es_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_752_, size_t v_i_753_, size_t v_stop_754_, lean_object* v_b_755_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_eq(v_i_753_, v_stop_754_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; size_t v___x_759_; size_t v___x_760_; 
v___x_757_ = lean_array_uget_borrowed(v_as_752_, v_i_753_);
lean_inc(v___x_757_);
v___x_758_ = l_Lean_addAliasEntry(v_b_755_, v___x_757_);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_add(v_i_753_, v___x_759_);
v_i_753_ = v___x_760_;
v_b_755_ = v___x_758_;
goto _start;
}
else
{
return v_b_755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_762_, lean_object* v_i_763_, lean_object* v_stop_764_, lean_object* v_b_765_){
_start:
{
size_t v_i_boxed_766_; size_t v_stop_boxed_767_; lean_object* v_res_768_; 
v_i_boxed_766_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_stop_boxed_767_ = lean_unbox_usize(v_stop_764_);
lean_dec(v_stop_764_);
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_762_, v_i_boxed_766_, v_stop_boxed_767_, v_b_765_);
lean_dec_ref(v_as_762_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_769_, size_t v_i_770_, size_t v_stop_771_, lean_object* v_b_772_){
_start:
{
lean_object* v___y_774_; uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_eq(v_i_770_, v_stop_771_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_779_ = lean_array_uget_borrowed(v_as_769_, v_i_770_);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_array_get_size(v___x_779_);
v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
v___y_774_ = v_b_772_;
goto v___jp_773_;
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_of_nat(v___x_781_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_779_, v___x_783_, v___x_784_, v_b_772_);
v___y_774_ = v___x_785_;
goto v___jp_773_;
}
}
else
{
return v_b_772_;
}
v___jp_773_:
{
size_t v___x_775_; size_t v___x_776_; 
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_770_, v___x_775_);
v_i_770_ = v___x_776_;
v_b_772_ = v___y_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_786_, lean_object* v_i_787_, lean_object* v_stop_788_, lean_object* v_b_789_){
_start:
{
size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v_i_boxed_790_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_788_);
lean_dec(v_stop_788_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_786_, v_i_boxed_790_, v_stop_boxed_791_, v_b_789_);
lean_dec_ref(v_as_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_793_, lean_object* v_as_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v_as_794_);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
return v_initState_793_;
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_796_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_794_, v___x_798_, v___x_799_, v_initState_793_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_801_, lean_object* v_as_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_801_, v_as_802_);
lean_dec_ref(v_as_802_);
return v_res_803_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_unsigned_to_nat(16u);
v___x_806_ = lean_mk_array(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; 
v___x_813_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_814_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_815_ = 1;
v___x_816_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_813_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*2, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_819_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_818_, v_es_817_);
v___x_820_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_821_);
lean_dec_ref(v_es_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_840_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_843_, lean_object* v_a_844_, lean_object* v_e_845_){
_start:
{
lean_object* v___x_846_; lean_object* v_toEnvExtension_847_; lean_object* v_asyncMode_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_846_ = l_Lean_aliasExtension;
v_toEnvExtension_847_ = lean_ctor_get(v___x_846_, 0);
v_asyncMode_848_ = lean_ctor_get(v_toEnvExtension_847_, 2);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_a_844_);
lean_ctor_set(v___x_849_, 1, v_e_845_);
v___x_850_ = lean_box(0);
v___x_851_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_846_, v_env_843_, v___x_849_, v_asyncMode_848_, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__0(void){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_SMap_instInhabited___redArg();
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_853_){
_start:
{
lean_object* v___x_854_; lean_object* v_toEnvExtension_855_; lean_object* v_asyncMode_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_854_ = l_Lean_aliasExtension;
v_toEnvExtension_855_ = lean_ctor_get(v___x_854_, 0);
v_asyncMode_856_ = lean_ctor_get(v_toEnvExtension_855_, 2);
v___x_857_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_858_ = lean_box(0);
v___x_859_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_857_, v___x_854_, v_env_853_, v_asyncMode_856_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_860_, uint8_t v_skipProtected_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
if (lean_obj_tag(v_a_862_) == 0)
{
lean_object* v___x_864_; 
lean_dec_ref(v_env_860_);
v___x_864_ = l_List_reverse___redArg(v_a_863_);
return v___x_864_;
}
else
{
lean_object* v_head_865_; lean_object* v_tail_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v_head_865_ = lean_ctor_get(v_a_862_, 0);
v_tail_866_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_877_ == 0)
{
v___x_868_ = v_a_862_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_tail_866_);
lean_inc(v_head_865_);
lean_dec(v_a_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
uint8_t v___x_870_; 
lean_inc(v_head_865_);
lean_inc_ref(v_env_860_);
v___x_870_ = l_Lean_isProtected(v_env_860_, v_head_865_);
if (v___x_870_ == 0)
{
if (v_skipProtected_861_ == 0)
{
lean_del_object(v___x_868_);
lean_dec(v_head_865_);
v_a_862_ = v_tail_866_;
goto _start;
}
else
{
lean_object* v___x_873_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_a_863_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_head_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_863_);
v___x_873_ = v_reuseFailAlloc_875_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v_a_862_ = v_tail_866_;
v_a_863_ = v___x_873_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_868_);
lean_dec(v_head_865_);
v_a_862_ = v_tail_866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_878_, lean_object* v_skipProtected_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
uint8_t v_skipProtected_boxed_882_; lean_object* v_res_883_; 
v_skipProtected_boxed_882_ = lean_unbox(v_skipProtected_879_);
v_res_883_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_878_, v_skipProtected_boxed_882_, v_a_880_, v_a_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_884_, lean_object* v_a_885_, uint8_t v_skipProtected_886_){
_start:
{
lean_object* v___x_887_; lean_object* v_toEnvExtension_888_; lean_object* v_asyncMode_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_887_ = l_Lean_aliasExtension;
v_toEnvExtension_888_ = lean_ctor_get(v___x_887_, 0);
v_asyncMode_889_ = lean_ctor_get(v_toEnvExtension_888_, 2);
v___x_890_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_891_ = lean_box(0);
lean_inc_ref(v_env_884_);
v___x_892_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_890_, v___x_887_, v_env_884_, v_asyncMode_889_, v___x_891_);
v___x_893_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_892_, v_a_885_);
lean_dec(v___x_892_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_894_; 
lean_dec_ref(v_env_884_);
v___x_894_ = lean_box(0);
return v___x_894_;
}
else
{
if (v_skipProtected_886_ == 0)
{
lean_object* v_val_895_; 
lean_dec_ref(v_env_884_);
v_val_895_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v___x_893_, 1);
return v_val_895_;
}
else
{
lean_object* v_val_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_val_896_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_893_, 1);
v___x_897_ = lean_box(0);
v___x_898_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_884_, v_skipProtected_886_, v_val_896_, v___x_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_899_, lean_object* v_a_900_, lean_object* v_skipProtected_901_){
_start:
{
uint8_t v_skipProtected_boxed_902_; lean_object* v_res_903_; 
v_skipProtected_boxed_902_ = lean_unbox(v_skipProtected_901_);
v_res_903_ = l_Lean_getAliases(v_env_899_, v_a_900_, v_skipProtected_boxed_902_);
lean_dec(v_a_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_904_, lean_object* v_as_905_, lean_object* v_a_906_, lean_object* v_es_907_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_904_, v_es_907_);
if (v___x_908_ == 0)
{
lean_dec(v_a_906_);
return v_as_905_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_a_906_);
lean_ctor_set(v___x_909_, 1, v_as_905_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_910_, lean_object* v_as_911_, lean_object* v_a_912_, lean_object* v_es_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_getRevAliases___lam__0(v_e_910_, v_as_911_, v_a_912_, v_es_913_);
lean_dec(v_es_913_);
lean_dec(v_e_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_915_, lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_i_918_, lean_object* v_acc_919_){
_start:
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_array_get_size(v_keys_916_);
v___x_921_ = lean_nat_dec_lt(v_i_918_, v___x_920_);
if (v___x_921_ == 0)
{
lean_dec(v_i_918_);
lean_dec(v_f_915_);
return v_acc_919_;
}
else
{
lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_k_922_ = lean_array_fget_borrowed(v_keys_916_, v_i_918_);
v_v_923_ = lean_array_fget_borrowed(v_vals_917_, v_i_918_);
lean_inc(v_f_915_);
lean_inc(v_v_923_);
lean_inc(v_k_922_);
v___x_924_ = lean_apply_3(v_f_915_, v_acc_919_, v_k_922_, v_v_923_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_i_918_, v___x_925_);
lean_dec(v_i_918_);
v_i_918_ = v___x_926_;
v_acc_919_ = v___x_924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_928_, lean_object* v_keys_929_, lean_object* v_vals_930_, lean_object* v_i_931_, lean_object* v_acc_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_928_, v_keys_929_, v_vals_930_, v_i_931_, v_acc_932_);
lean_dec_ref(v_vals_930_);
lean_dec_ref(v_keys_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_934_, lean_object* v_as_935_, size_t v_i_936_, size_t v_stop_937_, lean_object* v_b_938_){
_start:
{
lean_object* v___y_940_; uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_eq(v_i_936_, v_stop_937_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_array_uget_borrowed(v_as_935_, v_i_936_);
switch(lean_obj_tag(v___x_945_))
{
case 0:
{
lean_object* v_key_946_; lean_object* v_val_947_; lean_object* v___x_948_; 
v_key_946_ = lean_ctor_get(v___x_945_, 0);
v_val_947_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_f_934_);
lean_inc(v_val_947_);
lean_inc(v_key_946_);
v___x_948_ = lean_apply_3(v_f_934_, v_b_938_, v_key_946_, v_val_947_);
v___y_940_ = v___x_948_;
goto v___jp_939_;
}
case 1:
{
lean_object* v_node_949_; lean_object* v___x_950_; 
v_node_949_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_f_934_);
v___x_950_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_934_, v_node_949_, v_b_938_);
v___y_940_ = v___x_950_;
goto v___jp_939_;
}
default: 
{
v___y_940_ = v_b_938_;
goto v___jp_939_;
}
}
}
else
{
lean_dec(v_f_934_);
return v_b_938_;
}
v___jp_939_:
{
size_t v___x_941_; size_t v___x_942_; 
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_936_, v___x_941_);
v_i_936_ = v___x_942_;
v_b_938_ = v___y_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
lean_object* v_es_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_es_954_ = lean_ctor_get(v_x_952_, 0);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get_size(v_es_954_);
v___x_957_ = lean_nat_dec_lt(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_dec(v_f_951_);
return v_x_953_;
}
else
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_956_);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_951_, v_es_954_, v___x_958_, v___x_959_, v_x_953_);
return v___x_960_;
}
}
else
{
lean_object* v_ks_961_; lean_object* v_vs_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_ks_961_ = lean_ctor_get(v_x_952_, 0);
v_vs_962_ = lean_ctor_get(v_x_952_, 1);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_951_, v_ks_961_, v_vs_962_, v___x_963_, v_x_953_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_965_, v_x_966_, v_x_967_);
lean_dec_ref(v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_969_, lean_object* v_as_970_, lean_object* v_i_971_, lean_object* v_stop_972_, lean_object* v_b_973_){
_start:
{
size_t v_i_boxed_974_; size_t v_stop_boxed_975_; lean_object* v_res_976_; 
v_i_boxed_974_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_stop_boxed_975_ = lean_unbox_usize(v_stop_972_);
lean_dec(v_stop_972_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_969_, v_as_970_, v_i_boxed_974_, v_stop_boxed_975_, v_b_973_);
lean_dec_ref(v_as_970_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_977_, lean_object* v_x1_978_, lean_object* v_x2_979_, lean_object* v_x3_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = lean_apply_3(v_f_977_, v_x1_978_, v_x2_979_, v_x3_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_982_, lean_object* v_f_983_, lean_object* v_init_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___x_986_; 
v___f_985_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_985_, 0, v_f_983_);
v___x_986_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_985_, v_map_982_, v_init_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_987_, lean_object* v_f_988_, lean_object* v_init_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_987_, v_f_988_, v_init_989_);
lean_dec_ref(v_map_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_dec(v_f_991_);
return v_x_992_;
}
else
{
lean_object* v_key_994_; lean_object* v_value_995_; lean_object* v_tail_996_; lean_object* v___x_997_; 
v_key_994_ = lean_ctor_get(v_x_993_, 0);
lean_inc(v_key_994_);
v_value_995_ = lean_ctor_get(v_x_993_, 1);
lean_inc(v_value_995_);
v_tail_996_ = lean_ctor_get(v_x_993_, 2);
lean_inc(v_tail_996_);
lean_dec_ref_known(v_x_993_, 3);
lean_inc(v_f_991_);
v___x_997_ = lean_apply_3(v_f_991_, v_x_992_, v_key_994_, v_value_995_);
v_x_992_ = v___x_997_;
v_x_993_ = v_tail_996_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_999_, lean_object* v_as_1000_, size_t v_i_1001_, size_t v_stop_1002_, lean_object* v_b_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; 
v___x_1005_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
lean_inc(v___x_1005_);
lean_inc(v_f_999_);
v___x_1006_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_999_, v_b_1003_, v___x_1005_);
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_1001_, v___x_1007_);
v_i_1001_ = v___x_1008_;
v_b_1003_ = v___x_1006_;
goto _start;
}
else
{
lean_dec(v_f_999_);
return v_b_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1010_, lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_stop_1013_, lean_object* v_b_1014_){
_start:
{
size_t v_i_boxed_1015_; size_t v_stop_boxed_1016_; lean_object* v_res_1017_; 
v_i_boxed_1015_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_stop_boxed_1016_ = lean_unbox_usize(v_stop_1013_);
lean_dec(v_stop_1013_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1010_, v_as_1011_, v_i_boxed_1015_, v_stop_boxed_1016_, v_b_1014_);
lean_dec_ref(v_as_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1018_, lean_object* v_init_1019_, lean_object* v_m_1020_){
_start:
{
lean_object* v_map_u2081_1021_; lean_object* v_map_u2082_1022_; lean_object* v_buckets_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_map_u2081_1021_ = lean_ctor_get(v_m_1020_, 0);
v_map_u2082_1022_ = lean_ctor_get(v_m_1020_, 1);
v_buckets_1023_ = lean_ctor_get(v_map_u2081_1021_, 1);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_buckets_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1022_, v_f_1018_, v_init_1019_);
return v___x_1027_;
}
else
{
size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = lean_usize_of_nat(v___x_1025_);
lean_inc(v_f_1018_);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1018_, v_buckets_1023_, v___x_1028_, v___x_1029_, v_init_1019_);
v___x_1031_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1022_, v_f_1018_, v___x_1030_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1032_, lean_object* v_init_1033_, lean_object* v_m_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1032_, v_init_1033_, v_m_1034_);
lean_dec_ref(v_m_1034_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1036_, lean_object* v_e_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v_toEnvExtension_1039_; lean_object* v_asyncMode_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1038_ = l_Lean_aliasExtension;
v_toEnvExtension_1039_ = lean_ctor_get(v___x_1038_, 0);
v_asyncMode_1040_ = lean_ctor_get(v_toEnvExtension_1039_, 2);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1041_, 0, v_e_1037_);
v___x_1042_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1042_, v___x_1038_, v_env_1036_, v_asyncMode_1040_, v___x_1044_);
v___x_1046_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1041_, v___x_1043_, v___x_1045_);
lean_dec(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1047_, lean_object* v_00_u03c3_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_m_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1049_, v_init_1050_, v_m_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1053_, lean_object* v_00_u03c3_1054_, lean_object* v_f_1055_, lean_object* v_init_1056_, lean_object* v_m_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1053_, v_00_u03c3_1054_, v_f_1055_, v_init_1056_, v_m_1057_);
lean_dec_ref(v_m_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1059_, lean_object* v_00_u03c3_1060_, lean_object* v_f_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1061_, v_x_1062_, v_x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_map_1067_, lean_object* v_f_1068_, lean_object* v_init_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1067_, v_f_1068_, v_init_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_map_1073_, lean_object* v_f_1074_, lean_object* v_init_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1071_, v_00_u03b2_1072_, v_map_1073_, v_f_1074_, v_init_1075_);
lean_dec_ref(v_map_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1077_, lean_object* v_00_u03c3_1078_, lean_object* v_f_1079_, lean_object* v_as_1080_, size_t v_i_1081_, size_t v_stop_1082_, lean_object* v_b_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1079_, v_as_1080_, v_i_1081_, v_stop_1082_, v_b_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1085_, lean_object* v_00_u03c3_1086_, lean_object* v_f_1087_, lean_object* v_as_1088_, lean_object* v_i_1089_, lean_object* v_stop_1090_, lean_object* v_b_1091_){
_start:
{
size_t v_i_boxed_1092_; size_t v_stop_boxed_1093_; lean_object* v_res_1094_; 
v_i_boxed_1092_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_stop_boxed_1093_ = lean_unbox_usize(v_stop_1090_);
lean_dec(v_stop_1090_);
v_res_1094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1085_, v_00_u03c3_1086_, v_f_1087_, v_as_1088_, v_i_boxed_1092_, v_stop_boxed_1093_, v_b_1091_);
lean_dec_ref(v_as_1088_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1095_, lean_object* v_f_1096_, lean_object* v_init_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1096_, v_map_1095_, v_init_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1099_, lean_object* v_f_1100_, lean_object* v_init_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1099_, v_f_1100_, v_init_1101_);
lean_dec_ref(v_map_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1103_, lean_object* v_00_u03b2_1104_, lean_object* v_map_1105_, lean_object* v_f_1106_, lean_object* v_init_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1106_, v_map_1105_, v_init_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_map_1111_, lean_object* v_f_1112_, lean_object* v_init_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1109_, v_00_u03b2_1110_, v_map_1111_, v_f_1112_, v_init_1113_);
lean_dec_ref(v_map_1111_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1115_, lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_f_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1118_, v_x_1119_, v_x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1122_, lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_f_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1122_, v_00_u03b1_1123_, v_00_u03b2_1124_, v_f_1125_, v_x_1126_, v_x_1127_);
lean_dec_ref(v_x_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_00_u03c3_1131_, lean_object* v_f_1132_, lean_object* v_as_1133_, size_t v_i_1134_, size_t v_stop_1135_, lean_object* v_b_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1132_, v_as_1133_, v_i_1134_, v_stop_1135_, v_b_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_00_u03c3_1140_, lean_object* v_f_1141_, lean_object* v_as_1142_, lean_object* v_i_1143_, lean_object* v_stop_1144_, lean_object* v_b_1145_){
_start:
{
size_t v_i_boxed_1146_; size_t v_stop_boxed_1147_; lean_object* v_res_1148_; 
v_i_boxed_1146_ = lean_unbox_usize(v_i_1143_);
lean_dec(v_i_1143_);
v_stop_boxed_1147_ = lean_unbox_usize(v_stop_1144_);
lean_dec(v_stop_1144_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1138_, v_00_u03b2_1139_, v_00_u03c3_1140_, v_f_1141_, v_as_1142_, v_i_boxed_1146_, v_stop_boxed_1147_, v_b_1145_);
lean_dec_ref(v_as_1142_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1149_, lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_f_1152_, lean_object* v_keys_1153_, lean_object* v_vals_1154_, lean_object* v_heq_1155_, lean_object* v_i_1156_, lean_object* v_acc_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1152_, v_keys_1153_, v_vals_1154_, v_i_1156_, v_acc_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1159_, lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_f_1162_, lean_object* v_keys_1163_, lean_object* v_vals_1164_, lean_object* v_heq_1165_, lean_object* v_i_1166_, lean_object* v_acc_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1159_, v_00_u03b1_1160_, v_00_u03b2_1161_, v_f_1162_, v_keys_1163_, v_vals_1164_, v_heq_1165_, v_i_1166_, v_acc_1167_);
lean_dec_ref(v_vals_1164_);
lean_dec_ref(v_keys_1163_);
return v_res_1168_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1169_, lean_object* v_declName_1170_){
_start:
{
uint8_t v___y_1172_; uint8_t v___x_1175_; 
v___x_1175_ = l_Lean_Environment_containsOnBranch(v_env_1169_, v_declName_1170_);
if (v___x_1175_ == 0)
{
uint8_t v___x_1176_; 
lean_inc(v_declName_1170_);
lean_inc_ref(v_env_1169_);
v___x_1176_ = lean_is_reserved_name(v_env_1169_, v_declName_1170_);
v___y_1172_ = v___x_1176_;
goto v___jp_1171_;
}
else
{
v___y_1172_ = v___x_1175_;
goto v___jp_1171_;
}
v___jp_1171_:
{
if (v___y_1172_ == 0)
{
uint8_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 1;
v___x_1174_ = l_Lean_Environment_contains(v_env_1169_, v_declName_1170_, v___x_1173_);
return v___x_1174_;
}
else
{
lean_dec(v_declName_1170_);
lean_dec_ref(v_env_1169_);
return v___y_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1177_, lean_object* v_declName_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1177_, v_declName_1178_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1181_, lean_object* v_decl_1182_, lean_object* v_ref_1183_){
_start:
{
lean_object* v_defValue_1185_; lean_object* v_descr_1186_; lean_object* v_deprecation_x3f_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_defValue_1185_ = lean_ctor_get(v_decl_1182_, 0);
v_descr_1186_ = lean_ctor_get(v_decl_1182_, 1);
v_deprecation_x3f_1187_ = lean_ctor_get(v_decl_1182_, 2);
v___x_1188_ = lean_alloc_ctor(1, 0, 1);
v___x_1189_ = lean_unbox(v_defValue_1185_);
lean_ctor_set_uint8(v___x_1188_, 0, v___x_1189_);
lean_inc(v_deprecation_x3f_1187_);
lean_inc_ref(v_descr_1186_);
lean_inc_n(v_name_1181_, 2);
v___x_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1190_, 0, v_name_1181_);
lean_ctor_set(v___x_1190_, 1, v_ref_1183_);
lean_ctor_set(v___x_1190_, 2, v___x_1188_);
lean_ctor_set(v___x_1190_, 3, v_descr_1186_);
lean_ctor_set(v___x_1190_, 4, v_deprecation_x3f_1187_);
v___x_1191_ = lean_register_option(v_name_1181_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v___x_1191_, 0);
lean_dec(v_unused_1200_);
v___x_1193_ = v___x_1191_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v___x_1191_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
lean_inc(v_defValue_1185_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_name_1181_);
lean_ctor_set(v___x_1195_, 1, v_defValue_1185_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_name_1181_);
v_a_1201_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1191_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1209_, lean_object* v_decl_1210_, lean_object* v_ref_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1209_, v_decl_1210_, v_ref_1211_);
lean_dec_ref(v_decl_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1233_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1234_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1235_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1232_, v___x_1233_, v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1257_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1258_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1259_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1256_, v___x_1257_, v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1262_, lean_object* v_opt_1263_){
_start:
{
lean_object* v_name_1264_; lean_object* v_defValue_1265_; lean_object* v_map_1266_; lean_object* v___x_1267_; 
v_name_1264_ = lean_ctor_get(v_opt_1263_, 0);
v_defValue_1265_ = lean_ctor_get(v_opt_1263_, 1);
v_map_1266_ = lean_ctor_get(v_opts_1262_, 0);
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1266_, v_name_1264_);
if (lean_obj_tag(v___x_1267_) == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_unbox(v_defValue_1265_);
return v___x_1268_;
}
else
{
lean_object* v_val_1269_; 
v_val_1269_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1267_, 1);
if (lean_obj_tag(v_val_1269_) == 1)
{
uint8_t v_v_1270_; 
v_v_1270_ = lean_ctor_get_uint8(v_val_1269_, 0);
lean_dec_ref_known(v_val_1269_, 0);
return v_v_1270_;
}
else
{
uint8_t v___x_1271_; 
lean_dec(v_val_1269_);
v___x_1271_ = lean_unbox(v_defValue_1265_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1272_, lean_object* v_opt_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1272_, v_opt_1273_);
lean_dec_ref(v_opt_1273_);
lean_dec_ref(v_opts_1272_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1279_, lean_object* v_env_1280_, lean_object* v_as_1281_, size_t v_sz_1282_, size_t v_i_1283_, lean_object* v_b_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_usize_dec_lt(v_i_1283_, v_sz_1282_);
if (v___x_1285_ == 0)
{
lean_dec_ref(v_env_1280_);
lean_dec(v_declName_1279_);
lean_inc_ref(v_b_1284_);
return v_b_1284_;
}
else
{
lean_object* v_a_1286_; lean_object* v_toImport_1287_; lean_object* v_module_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_a_1286_ = lean_array_uget_borrowed(v_as_1281_, v_i_1283_);
v_toImport_1287_ = lean_ctor_get(v_a_1286_, 0);
v_module_1288_ = lean_ctor_get(v_toImport_1287_, 0);
v___x_1289_ = lean_box(0);
lean_inc(v_declName_1279_);
lean_inc(v_module_1288_);
v___x_1290_ = l_Lean_mkPrivateNameCore(v_module_1288_, v_declName_1279_);
lean_inc(v___x_1290_);
lean_inc_ref(v_env_1280_);
v___x_1291_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1280_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; 
lean_dec(v___x_1290_);
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1283_, v___x_1293_);
v_i_1283_ = v___x_1294_;
v_b_1284_ = v___x_1292_;
goto _start;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec_ref(v_env_1280_);
lean_dec(v_declName_1279_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1290_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1289_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1299_, lean_object* v_env_1300_, lean_object* v_as_1301_, lean_object* v_sz_1302_, lean_object* v_i_1303_, lean_object* v_b_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1302_);
lean_dec(v_sz_1302_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1299_, v_env_1300_, v_as_1301_, v_sz_boxed_1305_, v_i_boxed_1306_, v_b_1304_);
lean_dec_ref(v_b_1304_);
lean_dec_ref(v_as_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1308_, lean_object* v_opts_1309_, lean_object* v_declName_1310_){
_start:
{
uint8_t v_isExporting_1326_; 
v_isExporting_1326_ = lean_ctor_get_uint8(v_env_1308_, sizeof(void*)*8);
if (v_isExporting_1326_ == 0)
{
goto v___jp_1311_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1328_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1309_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v_declName_1310_);
lean_dec_ref(v_env_1308_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
else
{
goto v___jp_1311_;
}
}
v___jp_1311_:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
lean_inc(v_declName_1310_);
v___x_1312_ = l_Lean_mkPrivateName(v_env_1308_, v_declName_1310_);
lean_inc(v___x_1312_);
lean_inc_ref(v_env_1308_);
v___x_1313_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1308_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; uint8_t v_isModule_1315_; 
lean_dec(v___x_1312_);
v___x_1314_ = l_Lean_Environment_header(v_env_1308_);
v_isModule_1315_ = lean_ctor_get_uint8(v___x_1314_, sizeof(void*)*7 + 4);
if (v_isModule_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref(v___x_1314_);
lean_dec(v_declName_1310_);
lean_dec_ref(v_env_1308_);
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
else
{
lean_object* v_importAllModules_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; lean_object* v_fst_1323_; 
v_importAllModules_1317_ = lean_ctor_get(v___x_1314_, 5);
lean_inc_ref(v_importAllModules_1317_);
lean_dec_ref(v___x_1314_);
v___x_1318_ = lean_box(0);
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1320_ = lean_array_size(v_importAllModules_1317_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1310_, v_env_1308_, v_importAllModules_1317_, v_sz_1320_, v___x_1321_, v___x_1319_);
lean_dec_ref(v_importAllModules_1317_);
v_fst_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_fst_1323_);
lean_dec_ref(v___x_1322_);
if (lean_obj_tag(v_fst_1323_) == 0)
{
return v___x_1318_;
}
else
{
lean_object* v_val_1324_; 
v_val_1324_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v_fst_1323_, 1);
return v_val_1324_;
}
}
}
else
{
lean_object* v___x_1325_; 
lean_dec(v_declName_1310_);
lean_dec_ref(v_env_1308_);
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1312_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1330_, lean_object* v_opts_1331_, lean_object* v_declName_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1330_, v_opts_1331_, v_declName_1332_);
lean_dec_ref(v_opts_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1334_, lean_object* v_opts_1335_, lean_object* v_ns_1336_, lean_object* v_id_1337_){
_start:
{
lean_object* v_resolvedId_1338_; uint8_t v___x_1339_; lean_object* v_resolvedIds_1340_; 
lean_inc(v_id_1337_);
v_resolvedId_1338_ = l_Lean_Name_append(v_ns_1336_, v_id_1337_);
v___x_1339_ = l_Lean_Name_isAtomic(v_id_1337_);
lean_dec(v_id_1337_);
lean_inc_ref(v_env_1334_);
v_resolvedIds_1340_ = l_Lean_getAliases(v_env_1334_, v_resolvedId_1338_, v___x_1339_);
if (v___x_1339_ == 0)
{
goto v___jp_1341_;
}
else
{
uint8_t v___x_1347_; 
lean_inc(v_resolvedId_1338_);
lean_inc_ref(v_env_1334_);
v___x_1347_ = l_Lean_isProtected(v_env_1334_, v_resolvedId_1338_);
if (v___x_1347_ == 0)
{
goto v___jp_1341_;
}
else
{
lean_dec(v_resolvedId_1338_);
lean_dec_ref(v_env_1334_);
return v_resolvedIds_1340_;
}
}
v___jp_1341_:
{
uint8_t v___x_1342_; 
lean_inc(v_resolvedId_1338_);
lean_inc_ref(v_env_1334_);
v___x_1342_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1334_, v_resolvedId_1338_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1334_, v_opts_1335_, v_resolvedId_1338_);
if (lean_obj_tag(v___x_1343_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1345_; 
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_val_1344_);
lean_ctor_set(v___x_1345_, 1, v_resolvedIds_1340_);
return v___x_1345_;
}
else
{
lean_dec(v___x_1343_);
return v_resolvedIds_1340_;
}
}
else
{
lean_object* v___x_1346_; 
lean_dec_ref(v_env_1334_);
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_resolvedId_1338_);
lean_ctor_set(v___x_1346_, 1, v_resolvedIds_1340_);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1348_, lean_object* v_opts_1349_, lean_object* v_ns_1350_, lean_object* v_id_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1348_, v_opts_1349_, v_ns_1350_, v_id_1351_);
lean_dec_ref(v_opts_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1353_, lean_object* v_opts_1354_, lean_object* v_id_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 1)
{
lean_object* v_pre_1357_; lean_object* v___x_1358_; 
v_pre_1357_ = lean_ctor_get(v_x_1356_, 0);
lean_inc(v_pre_1357_);
lean_inc(v_id_1355_);
lean_inc_ref(v_env_1353_);
v___x_1358_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1353_, v_opts_1354_, v_x_1356_, v_id_1355_);
if (lean_obj_tag(v___x_1358_) == 0)
{
v_x_1356_ = v_pre_1357_;
goto _start;
}
else
{
lean_dec(v_pre_1357_);
lean_dec(v_id_1355_);
lean_dec_ref(v_env_1353_);
return v___x_1358_;
}
}
else
{
lean_object* v___x_1360_; 
lean_dec(v_x_1356_);
lean_dec(v_id_1355_);
lean_dec_ref(v_env_1353_);
v___x_1360_ = lean_box(0);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1361_, lean_object* v_opts_1362_, lean_object* v_id_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1361_, v_opts_1362_, v_id_1363_, v_x_1364_);
lean_dec_ref(v_opts_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1366_, lean_object* v_opts_1367_, lean_object* v_id_1368_){
_start:
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_Name_isAtomic(v_id_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_resolvedId_1372_; uint8_t v___x_1373_; 
v___x_1370_ = l_Lean_rootNamespace;
v___x_1371_ = lean_box(0);
v_resolvedId_1372_ = l_Lean_Name_replacePrefix(v_id_1368_, v___x_1370_, v___x_1371_);
lean_inc(v_resolvedId_1372_);
lean_inc_ref(v_env_1366_);
v___x_1373_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1366_, v_resolvedId_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1366_, v_opts_1367_, v_resolvedId_1372_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; 
lean_dec_ref(v_env_1366_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_resolvedId_1372_);
return v___x_1375_;
}
}
else
{
lean_object* v___x_1376_; 
lean_dec(v_id_1368_);
lean_dec_ref(v_env_1366_);
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1377_, lean_object* v_opts_1378_, lean_object* v_id_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1377_, v_opts_1378_, v_id_1379_);
lean_dec_ref(v_opts_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1381_, lean_object* v_opts_1382_, lean_object* v_id_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_dec(v_id_1383_);
lean_dec_ref(v_env_1381_);
return v_x_1385_;
}
else
{
lean_object* v_head_1386_; 
v_head_1386_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_head_1386_);
if (lean_obj_tag(v_head_1386_) == 0)
{
lean_object* v_tail_1387_; lean_object* v_ns_1388_; lean_object* v_except_1389_; uint8_t v___x_1390_; 
v_tail_1387_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_tail_1387_);
lean_dec_ref_known(v_x_1384_, 2);
v_ns_1388_ = lean_ctor_get(v_head_1386_, 0);
lean_inc(v_ns_1388_);
v_except_1389_ = lean_ctor_get(v_head_1386_, 1);
lean_inc(v_except_1389_);
lean_dec_ref_known(v_head_1386_, 2);
v___x_1390_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1383_, v_except_1389_);
lean_dec(v_except_1389_);
if (v___x_1390_ == 0)
{
lean_object* v_newResolvedIds_1391_; lean_object* v___x_1392_; 
lean_inc(v_id_1383_);
lean_inc_ref(v_env_1381_);
v_newResolvedIds_1391_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1381_, v_opts_1382_, v_ns_1388_, v_id_1383_);
v___x_1392_ = l_List_appendTR___redArg(v_newResolvedIds_1391_, v_x_1385_);
v_x_1384_ = v_tail_1387_;
v_x_1385_ = v___x_1392_;
goto _start;
}
else
{
lean_dec(v_ns_1388_);
v_x_1384_ = v_tail_1387_;
goto _start;
}
}
else
{
lean_object* v_tail_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1415_; 
v_tail_1395_ = lean_ctor_get(v_x_1384_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1416_);
v___x_1397_ = v_x_1384_;
v_isShared_1398_ = v_isSharedCheck_1415_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_tail_1395_);
lean_dec(v_x_1384_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1415_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_id_1399_; lean_object* v_declName_1400_; uint8_t v___x_1401_; 
v_id_1399_ = lean_ctor_get(v_head_1386_, 0);
lean_inc(v_id_1399_);
v_declName_1400_ = lean_ctor_get(v_head_1386_, 1);
lean_inc(v_declName_1400_);
lean_dec_ref_known(v_head_1386_, 2);
v___x_1401_ = lean_name_eq(v_id_1399_, v_id_1383_);
if (v___x_1401_ == 0)
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Lean_Name_isPrefixOf(v_id_1399_, v_id_1383_);
if (v___x_1402_ == 0)
{
lean_dec(v_declName_1400_);
lean_dec(v_id_1399_);
lean_del_object(v___x_1397_);
v_x_1384_ = v_tail_1395_;
goto _start;
}
else
{
lean_object* v_candidate_1404_; uint8_t v___x_1405_; 
lean_inc(v_id_1383_);
v_candidate_1404_ = l_Lean_Name_replacePrefix(v_id_1383_, v_id_1399_, v_declName_1400_);
lean_dec(v_declName_1400_);
lean_dec(v_id_1399_);
lean_inc(v_candidate_1404_);
lean_inc_ref(v_env_1381_);
v___x_1405_ = l_Lean_Environment_contains(v_env_1381_, v_candidate_1404_, v___x_1402_);
if (v___x_1405_ == 0)
{
lean_dec(v_candidate_1404_);
lean_del_object(v___x_1397_);
v_x_1384_ = v_tail_1395_;
goto _start;
}
else
{
lean_object* v___x_1408_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v_x_1385_);
lean_ctor_set(v___x_1397_, 0, v_candidate_1404_);
v___x_1408_ = v___x_1397_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_candidate_1404_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_x_1385_);
v___x_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
v_x_1384_ = v_tail_1395_;
v_x_1385_ = v___x_1408_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1412_; 
lean_dec(v_id_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v_x_1385_);
lean_ctor_set(v___x_1397_, 0, v_declName_1400_);
v___x_1412_ = v___x_1397_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_declName_1400_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_x_1385_);
v___x_1412_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
v_x_1384_ = v_tail_1395_;
v_x_1385_ = v___x_1412_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1417_, lean_object* v_opts_1418_, lean_object* v_id_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1417_, v_opts_1418_, v_id_1419_, v_x_1420_, v_x_1421_);
lean_dec_ref(v_opts_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1424_){
_start:
{
lean_object* v___f_1425_; lean_object* v___x_1426_; 
v___f_1425_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1426_ = l_List_eraseDupsBy___redArg(v___f_1425_, v_as_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_projs_1427_);
v___x_1430_ = l_List_reverse___redArg(v_a_1429_);
return v___x_1430_;
}
else
{
lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1441_; 
v_head_1431_ = lean_ctor_get(v_a_1428_, 0);
v_tail_1432_ = lean_ctor_get(v_a_1428_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1434_ = v_a_1428_;
v_isShared_1435_ = v_isSharedCheck_1441_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_tail_1432_);
lean_inc(v_head_1431_);
lean_dec(v_a_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1441_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_inc(v_projs_1427_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_head_1431_);
lean_ctor_set(v___x_1436_, 1, v_projs_1427_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_a_1429_);
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_a_1429_);
v___x_1438_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
v_a_1428_ = v_tail_1432_;
v_a_1429_ = v___x_1438_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1442_, lean_object* v_opts_1443_, lean_object* v_ns_1444_, lean_object* v_openDecls_1445_, lean_object* v_extractionResult_1446_, lean_object* v_id_1447_, lean_object* v_projs_1448_){
_start:
{
if (lean_obj_tag(v_id_1447_) == 1)
{
lean_object* v_pre_1449_; lean_object* v_str_1450_; lean_object* v_imported_1451_; lean_object* v_ctx_1452_; lean_object* v_scopes_1453_; lean_object* v___x_1454_; lean_object* v_id_1455_; lean_object* v___y_1457_; lean_object* v___x_1467_; lean_object* v___y_1469_; 
v_pre_1449_ = lean_ctor_get(v_id_1447_, 0);
lean_inc(v_pre_1449_);
v_str_1450_ = lean_ctor_get(v_id_1447_, 1);
lean_inc_ref(v_str_1450_);
v_imported_1451_ = lean_ctor_get(v_extractionResult_1446_, 1);
v_ctx_1452_ = lean_ctor_get(v_extractionResult_1446_, 2);
v_scopes_1453_ = lean_ctor_get(v_extractionResult_1446_, 3);
lean_inc(v_scopes_1453_);
lean_inc(v_ctx_1452_);
lean_inc(v_imported_1451_);
v___x_1454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1454_, 0, v_id_1447_);
lean_ctor_set(v___x_1454_, 1, v_imported_1451_);
lean_ctor_set(v___x_1454_, 2, v_ctx_1452_);
lean_ctor_set(v___x_1454_, 3, v_scopes_1453_);
v_id_1455_ = l_Lean_MacroScopesView_review(v___x_1454_);
lean_inc(v_ns_1444_);
lean_inc(v_id_1455_);
lean_inc_ref(v_env_1442_);
v___x_1467_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1442_, v_opts_1443_, v_id_1455_, v_ns_1444_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1474_; 
lean_inc(v_id_1455_);
lean_inc_ref(v_env_1442_);
v___x_1474_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1442_, v_opts_1443_, v_id_1455_);
if (lean_obj_tag(v___x_1474_) == 0)
{
uint8_t v___x_1475_; 
lean_inc(v_id_1455_);
lean_inc_ref(v_env_1442_);
v___x_1475_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1442_, v_id_1455_);
if (v___x_1475_ == 0)
{
v___y_1469_ = v___x_1467_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1476_; 
lean_inc(v_id_1455_);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_id_1455_);
lean_ctor_set(v___x_1476_, 1, v___x_1467_);
v___y_1469_ = v___x_1476_;
goto v___jp_1468_;
}
}
else
{
lean_object* v_val_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec(v_id_1455_);
lean_dec_ref(v_str_1450_);
lean_dec(v_pre_1449_);
lean_dec(v_openDecls_1445_);
lean_dec(v_ns_1444_);
lean_dec_ref(v_env_1442_);
v_val_1477_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_val_1477_);
lean_ctor_set(v___x_1478_, 1, v_projs_1448_);
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
return v___x_1480_;
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_id_1455_);
lean_dec_ref(v_str_1450_);
lean_dec(v_pre_1449_);
lean_dec(v_openDecls_1445_);
lean_dec(v_ns_1444_);
lean_dec_ref(v_env_1442_);
v___x_1481_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1467_);
v___x_1482_ = lean_box(0);
v___x_1483_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1448_, v___x_1481_, v___x_1482_);
return v___x_1483_;
}
v___jp_1456_:
{
lean_object* v_resolvedIds_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v_resolvedIds_1461_; 
lean_inc(v_openDecls_1445_);
lean_inc(v_id_1455_);
lean_inc_ref_n(v_env_1442_, 2);
v_resolvedIds_1458_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1442_, v_opts_1443_, v_id_1455_, v_openDecls_1445_, v___y_1457_);
v___x_1459_ = l_Lean_Name_isAtomic(v_id_1455_);
v___x_1460_ = l_Lean_getAliases(v_env_1442_, v_id_1455_, v___x_1459_);
lean_dec(v_id_1455_);
v_resolvedIds_1461_ = l_List_appendTR___redArg(v___x_1460_, v_resolvedIds_1458_);
if (lean_obj_tag(v_resolvedIds_1461_) == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_str_1450_);
lean_ctor_set(v___x_1462_, 1, v_projs_1448_);
v_id_1447_ = v_pre_1449_;
v_projs_1448_ = v___x_1462_;
goto _start;
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec_ref(v_str_1450_);
lean_dec(v_pre_1449_);
lean_dec(v_openDecls_1445_);
lean_dec(v_ns_1444_);
lean_dec_ref(v_env_1442_);
v___x_1464_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1461_);
v___x_1465_ = lean_box(0);
v___x_1466_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1448_, v___x_1464_, v___x_1465_);
return v___x_1466_;
}
}
v___jp_1468_:
{
lean_object* v___x_1470_; 
lean_inc(v_id_1455_);
lean_inc_ref(v_env_1442_);
v___x_1470_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1442_, v_opts_1443_, v_id_1455_);
if (lean_obj_tag(v___x_1470_) == 1)
{
lean_object* v_val_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_val_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_val_1471_);
lean_ctor_set(v___x_1472_, 1, v___x_1467_);
v___x_1473_ = l_List_appendTR___redArg(v___x_1472_, v___y_1469_);
v___y_1457_ = v___x_1473_;
goto v___jp_1456_;
}
else
{
lean_dec(v___x_1470_);
lean_dec(v___x_1467_);
v___y_1457_ = v___y_1469_;
goto v___jp_1456_;
}
}
}
else
{
lean_object* v___x_1484_; 
lean_dec(v_projs_1448_);
lean_dec(v_id_1447_);
lean_dec(v_openDecls_1445_);
lean_dec(v_ns_1444_);
lean_dec_ref(v_env_1442_);
v___x_1484_ = lean_box(0);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1485_, lean_object* v_opts_1486_, lean_object* v_ns_1487_, lean_object* v_openDecls_1488_, lean_object* v_extractionResult_1489_, lean_object* v_id_1490_, lean_object* v_projs_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1485_, v_opts_1486_, v_ns_1487_, v_openDecls_1488_, v_extractionResult_1489_, v_id_1490_, v_projs_1491_);
lean_dec_ref(v_extractionResult_1489_);
lean_dec_ref(v_opts_1486_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1493_, lean_object* v_opts_1494_, lean_object* v_ns_1495_, lean_object* v_openDecls_1496_, lean_object* v_id_1497_){
_start:
{
lean_object* v_extractionResult_1498_; lean_object* v_name_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_extractionResult_1498_ = l_Lean_extractMacroScopes(v_id_1497_);
v_name_1499_ = lean_ctor_get(v_extractionResult_1498_, 0);
lean_inc(v_name_1499_);
v___x_1500_ = lean_box(0);
v___x_1501_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1493_, v_opts_1494_, v_ns_1495_, v_openDecls_1496_, v_extractionResult_1498_, v_name_1499_, v___x_1500_);
lean_dec_ref(v_extractionResult_1498_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1502_, lean_object* v_opts_1503_, lean_object* v_ns_1504_, lean_object* v_openDecls_1505_, lean_object* v_id_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_ResolveName_resolveGlobalName(v_env_1502_, v_opts_1503_, v_ns_1504_, v_openDecls_1505_, v_id_1506_);
lean_dec_ref(v_opts_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_panic_fn_borrowed(v___x_1509_, v_msg_1508_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1514_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1515_ = lean_unsigned_to_nat(9u);
v___x_1516_ = lean_unsigned_to_nat(230u);
v___x_1517_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1518_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1519_ = l_mkPanicMessageWithDecl(v___x_1518_, v___x_1517_, v___x_1516_, v___x_1515_, v___x_1514_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1520_, lean_object* v_n_1521_, lean_object* v_ns_1522_){
_start:
{
switch(lean_obj_tag(v_ns_1522_))
{
case 1:
{
lean_object* v_pre_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_pre_1523_ = lean_ctor_get(v_ns_1522_, 0);
lean_inc(v_pre_1523_);
lean_inc(v_n_1521_);
v___x_1524_ = l_Lean_Name_append(v_ns_1522_, v_n_1521_);
lean_inc_ref(v_env_1520_);
v___x_1525_ = l_Lean_Environment_isNamespace(v_env_1520_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec(v___x_1524_);
v_ns_1522_ = v_pre_1523_;
goto _start;
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_pre_1523_);
lean_dec(v_n_1521_);
lean_dec_ref(v_env_1520_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1524_);
return v___x_1527_;
}
}
case 0:
{
lean_object* v___x_1528_; lean_object* v_n_1529_; uint8_t v___x_1530_; 
v___x_1528_ = l_Lean_rootNamespace;
v_n_1529_ = l_Lean_Name_replacePrefix(v_n_1521_, v___x_1528_, v_ns_1522_);
v___x_1530_ = l_Lean_Environment_isNamespace(v_env_1520_, v_n_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_dec(v_n_1529_);
v___x_1531_ = lean_box(0);
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_n_1529_);
return v___x_1532_;
}
}
default: 
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_ns_1522_);
lean_dec(v_n_1521_);
lean_dec_ref(v_env_1520_);
v___x_1533_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1534_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1533_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1535_, lean_object* v_n_1536_, lean_object* v_x_1537_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_object* v___x_1538_; 
lean_dec(v_n_1536_);
lean_dec_ref(v_env_1535_);
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
else
{
lean_object* v_head_1539_; 
v_head_1539_ = lean_ctor_get(v_x_1537_, 0);
if (lean_obj_tag(v_head_1539_) == 0)
{
lean_object* v_tail_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1557_; 
lean_inc_ref(v_head_1539_);
v_tail_1540_ = lean_ctor_get(v_x_1537_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_x_1537_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_x_1537_, 0);
lean_dec(v_unused_1558_);
v___x_1542_ = v_x_1537_;
v_isShared_1543_ = v_isSharedCheck_1557_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_tail_1540_);
lean_dec(v_x_1537_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1557_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_ns_1544_; lean_object* v_except_1545_; lean_object* v___x_1546_; uint8_t v___y_1548_; uint8_t v___x_1554_; 
v_ns_1544_ = lean_ctor_get(v_head_1539_, 0);
lean_inc(v_ns_1544_);
v_except_1545_ = lean_ctor_get(v_head_1539_, 1);
lean_inc(v_except_1545_);
lean_dec_ref_known(v_head_1539_, 2);
lean_inc(v_n_1536_);
v___x_1546_ = l_Lean_Name_append(v_ns_1544_, v_n_1536_);
lean_inc_ref(v_env_1535_);
v___x_1554_ = l_Lean_Environment_isNamespace(v_env_1535_, v___x_1546_);
if (v___x_1554_ == 0)
{
lean_dec(v_except_1545_);
v___y_1548_ = v___x_1554_;
goto v___jp_1547_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1536_, v_except_1545_);
lean_dec(v_except_1545_);
if (v___x_1555_ == 0)
{
v___y_1548_ = v___x_1554_;
goto v___jp_1547_;
}
else
{
lean_dec(v___x_1546_);
lean_del_object(v___x_1542_);
v_x_1537_ = v_tail_1540_;
goto _start;
}
}
v___jp_1547_:
{
if (v___y_1548_ == 0)
{
lean_dec(v___x_1546_);
lean_del_object(v___x_1542_);
v_x_1537_ = v_tail_1540_;
goto _start;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1535_, v_n_1536_, v_tail_1540_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___x_1550_);
lean_ctor_set(v___x_1542_, 0, v___x_1546_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_object* v_tail_1559_; 
v_tail_1559_ = lean_ctor_get(v_x_1537_, 1);
lean_inc(v_tail_1559_);
lean_dec_ref_known(v_x_1537_, 2);
v_x_1537_ = v_tail_1559_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1561_, lean_object* v_ns_1562_, lean_object* v_openDecls_1563_, lean_object* v_id_1564_){
_start:
{
lean_object* v___x_1565_; 
lean_inc(v_id_1564_);
lean_inc_ref(v_env_1561_);
v___x_1565_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1561_, v_id_1564_, v_ns_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1561_, v_id_1564_, v_openDecls_1563_);
return v___x_1566_;
}
else
{
lean_object* v_val_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_val_1567_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1568_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1561_, v_id_1564_, v_openDecls_1563_);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_val_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1570_, lean_object* v_inst_1571_){
_start:
{
lean_object* v_getCurrNamespace_1572_; lean_object* v_getOpenDecls_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1582_; 
v_getCurrNamespace_1572_ = lean_ctor_get(v_inst_1571_, 0);
v_getOpenDecls_1573_ = lean_ctor_get(v_inst_1571_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_inst_1571_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1575_ = v_inst_1571_;
v_isShared_1576_ = v_isSharedCheck_1582_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_getOpenDecls_1573_);
lean_inc(v_getCurrNamespace_1572_);
lean_dec(v_inst_1571_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1582_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_inc(v_inst_1570_);
v___x_1577_ = lean_apply_2(v_inst_1570_, lean_box(0), v_getCurrNamespace_1572_);
v___x_1578_ = lean_apply_2(v_inst_1570_, lean_box(0), v_getOpenDecls_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1578_);
lean_ctor_set(v___x_1575_, 0, v___x_1577_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1583_, lean_object* v_n_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1585_, v_inst_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1594_, lean_object* v_toPure_1595_, lean_object* v_id_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, uint8_t v_____do__lift_1601_){
_start:
{
uint8_t v_isExporting_1605_; 
v_isExporting_1605_ = lean_ctor_get_uint8(v_____do__lift_1594_, sizeof(void*)*8);
if (v_isExporting_1605_ == 0)
{
lean_dec_ref(v_inst_1600_);
lean_dec(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec_ref(v_inst_1597_);
lean_dec(v_id_1596_);
goto v___jp_1602_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_isPrivateName(v_id_1596_);
if (v___x_1606_ == 0)
{
lean_dec_ref(v_inst_1600_);
lean_dec(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec_ref(v_inst_1597_);
lean_dec(v_id_1596_);
goto v___jp_1602_;
}
else
{
if (v_____do__lift_1601_ == 0)
{
lean_dec_ref(v_inst_1600_);
lean_dec(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec_ref(v_inst_1597_);
lean_dec(v_id_1596_);
goto v___jp_1602_;
}
else
{
lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v_toPure_1595_);
v___x_1607_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1608_ = 0;
v___x_1609_ = l_Lean_MessageData_ofConstName(v_id_1596_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1607_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_logWarning___redArg(v_inst_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v___x_1612_);
return v___x_1613_;
}
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_apply_2(v_toPure_1595_, lean_box(0), v___x_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1614_, lean_object* v_toPure_1615_, lean_object* v_id_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_____do__lift_1621_){
_start:
{
uint8_t v_____do__lift_199__boxed_1622_; lean_object* v_res_1623_; 
v_____do__lift_199__boxed_1622_ = lean_unbox(v_____do__lift_1621_);
v_res_1623_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1614_, v_toPure_1615_, v_id_1616_, v_inst_1617_, v_inst_1618_, v_inst_1619_, v_inst_1620_, v_____do__lift_199__boxed_1622_);
lean_dec_ref(v_____do__lift_1614_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1624_, lean_object* v_id_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v___x_1630_, lean_object* v_toBind_1631_, lean_object* v_____do__lift_1632_){
_start:
{
lean_object* v___f_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref(v_inst_1629_);
lean_inc_ref(v_inst_1626_);
v___f_1633_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1633_, 0, v_____do__lift_1632_);
lean_closure_set(v___f_1633_, 1, v_toPure_1624_);
lean_closure_set(v___f_1633_, 2, v_id_1625_);
lean_closure_set(v___f_1633_, 3, v_inst_1626_);
lean_closure_set(v___f_1633_, 4, v_inst_1627_);
lean_closure_set(v___f_1633_, 5, v_inst_1628_);
lean_closure_set(v___f_1633_, 6, v_inst_1629_);
v___x_1634_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1635_ = l_Lean_Option_getM___redArg(v_inst_1626_, v_inst_1629_, v___x_1630_, v___x_1634_);
v___x_1636_ = lean_apply_4(v_toBind_1631_, lean_box(0), lean_box(0), v___x_1635_, v___f_1633_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_id_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v_toApplicative_1644_; lean_object* v_toBind_1645_; lean_object* v_getEnv_1646_; lean_object* v_toPure_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; 
v___x_1643_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1644_ = lean_ctor_get(v_inst_1637_, 0);
v_toBind_1645_ = lean_ctor_get(v_inst_1637_, 1);
lean_inc_n(v_toBind_1645_, 2);
v_getEnv_1646_ = lean_ctor_get(v_inst_1638_, 0);
lean_inc(v_getEnv_1646_);
lean_dec_ref(v_inst_1638_);
v_toPure_1647_ = lean_ctor_get(v_toApplicative_1644_, 1);
lean_inc(v_toPure_1647_);
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1648_, 0, v_toPure_1647_);
lean_closure_set(v___f_1648_, 1, v_id_1642_);
lean_closure_set(v___f_1648_, 2, v_inst_1637_);
lean_closure_set(v___f_1648_, 3, v_inst_1640_);
lean_closure_set(v___f_1648_, 4, v_inst_1641_);
lean_closure_set(v___f_1648_, 5, v_inst_1639_);
lean_closure_set(v___f_1648_, 6, v___x_1643_);
lean_closure_set(v___f_1648_, 7, v_toBind_1645_);
v___x_1649_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v_getEnv_1646_, v___f_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_id_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1651_, v_inst_1652_, v_inst_1653_, v_inst_1654_, v_inst_1655_, v_id_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1658_, lean_object* v_n_1659_, lean_object* v_toPure_1660_, uint8_t v___y_1661_, uint8_t v___x_1662_, lean_object* v_____r_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1658_, v_n_1659_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_box(v___y_1661_);
v___x_1666_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___x_1665_);
return v___x_1666_;
}
else
{
lean_object* v_val_1667_; lean_object* v___x_1668_; uint8_t v_isModule_1669_; 
v_val_1667_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1668_ = l_Lean_Environment_header(v_env_1658_);
v_isModule_1669_ = lean_ctor_get_uint8(v___x_1668_, sizeof(void*)*7 + 4);
if (v_isModule_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v___x_1668_);
lean_dec(v_val_1667_);
v___x_1670_ = lean_box(v___x_1662_);
v___x_1671_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v_modules_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_modules_1672_ = lean_ctor_get(v___x_1668_, 3);
lean_inc_ref(v_modules_1672_);
lean_dec_ref(v___x_1668_);
v___x_1673_ = lean_array_get_size(v_modules_1672_);
v___x_1674_ = lean_nat_dec_lt(v_val_1667_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec_ref(v_modules_1672_);
lean_dec(v_val_1667_);
v___x_1675_ = lean_box(v_isModule_1669_);
v___x_1676_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___x_1675_);
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; lean_object* v_toImport_1678_; uint8_t v_importAll_1679_; 
v___x_1677_ = lean_array_fget(v_modules_1672_, v_val_1667_);
lean_dec(v_val_1667_);
lean_dec_ref(v_modules_1672_);
v_toImport_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc_ref(v_toImport_1678_);
lean_dec(v___x_1677_);
v_importAll_1679_ = lean_ctor_get_uint8(v_toImport_1678_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1678_);
if (v_importAll_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_box(v_isModule_1669_);
v___x_1681_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___x_1680_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_box(v___y_1661_);
v___x_1683_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___x_1682_);
return v___x_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1684_, lean_object* v_n_1685_, lean_object* v_toPure_1686_, lean_object* v___y_1687_, lean_object* v___x_1688_, lean_object* v_____r_1689_){
_start:
{
uint8_t v___y_386__boxed_1690_; uint8_t v___x_387__boxed_1691_; lean_object* v_res_1692_; 
v___y_386__boxed_1690_ = lean_unbox(v___y_1687_);
v___x_387__boxed_1691_ = lean_unbox(v___x_1688_);
v_res_1692_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1684_, v_n_1685_, v_toPure_1686_, v___y_386__boxed_1690_, v___x_387__boxed_1691_, v_____r_1689_);
lean_dec(v_n_1685_);
lean_dec_ref(v_env_1684_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1693_, lean_object* v_n_1694_, lean_object* v_toPure_1695_, uint8_t v___x_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_toBind_1702_, uint8_t v___y_1703_, uint8_t v_____do__lift_1704_){
_start:
{
uint8_t v___y_1706_; uint8_t v_isExporting_1712_; 
v_isExporting_1712_ = lean_ctor_get_uint8(v_env_1693_, sizeof(void*)*8);
if (v_isExporting_1712_ == 0)
{
v___y_1706_ = v___y_1703_;
goto v___jp_1705_;
}
else
{
if (v_____do__lift_1704_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_toBind_1702_);
lean_dec(v_inst_1701_);
lean_dec_ref(v_inst_1700_);
lean_dec_ref(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
lean_dec(v_n_1694_);
lean_dec_ref(v_env_1693_);
v___x_1713_ = lean_box(v___x_1696_);
v___x_1714_ = lean_apply_2(v_toPure_1695_, lean_box(0), v___x_1713_);
return v___x_1714_;
}
else
{
v___y_1706_ = v___y_1703_;
goto v___jp_1705_;
}
}
v___jp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1707_ = lean_box(v___y_1706_);
v___x_1708_ = lean_box(v___x_1696_);
lean_inc(v_n_1694_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1709_, 0, v_env_1693_);
lean_closure_set(v___f_1709_, 1, v_n_1694_);
lean_closure_set(v___f_1709_, 2, v_toPure_1695_);
lean_closure_set(v___f_1709_, 3, v___x_1707_);
lean_closure_set(v___f_1709_, 4, v___x_1708_);
v___x_1710_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1697_, v_inst_1698_, v_inst_1699_, v_inst_1700_, v_inst_1701_, v_n_1694_);
v___x_1711_ = lean_apply_4(v_toBind_1702_, lean_box(0), lean_box(0), v___x_1710_, v___f_1709_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1715_, lean_object* v_n_1716_, lean_object* v_toPure_1717_, lean_object* v___x_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_toBind_1724_, lean_object* v___y_1725_, lean_object* v_____do__lift_1726_){
_start:
{
uint8_t v___x_427__boxed_1727_; uint8_t v___y_433__boxed_1728_; uint8_t v_____do__lift_434__boxed_1729_; lean_object* v_res_1730_; 
v___x_427__boxed_1727_ = lean_unbox(v___x_1718_);
v___y_433__boxed_1728_ = lean_unbox(v___y_1725_);
v_____do__lift_434__boxed_1729_ = lean_unbox(v_____do__lift_1726_);
v_res_1730_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1715_, v_n_1716_, v_toPure_1717_, v___x_427__boxed_1727_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_toBind_1724_, v___y_433__boxed_1728_, v_____do__lift_434__boxed_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1731_, lean_object* v_toPure_1732_, uint8_t v___x_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_toBind_1739_, uint8_t v___y_1740_, lean_object* v___x_1741_, lean_object* v_env_1742_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1743_ = lean_box(v___x_1733_);
v___x_1744_ = lean_box(v___y_1740_);
lean_inc(v_toBind_1739_);
lean_inc_ref(v_inst_1736_);
lean_inc_ref(v_inst_1734_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1745_, 0, v_env_1742_);
lean_closure_set(v___f_1745_, 1, v_n_1731_);
lean_closure_set(v___f_1745_, 2, v_toPure_1732_);
lean_closure_set(v___f_1745_, 3, v___x_1743_);
lean_closure_set(v___f_1745_, 4, v_inst_1734_);
lean_closure_set(v___f_1745_, 5, v_inst_1735_);
lean_closure_set(v___f_1745_, 6, v_inst_1736_);
lean_closure_set(v___f_1745_, 7, v_inst_1737_);
lean_closure_set(v___f_1745_, 8, v_inst_1738_);
lean_closure_set(v___f_1745_, 9, v_toBind_1739_);
lean_closure_set(v___f_1745_, 10, v___x_1744_);
v___x_1746_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1747_ = l_Lean_Option_getM___redArg(v_inst_1734_, v_inst_1736_, v___x_1741_, v___x_1746_);
v___x_1748_ = lean_apply_4(v_toBind_1739_, lean_box(0), lean_box(0), v___x_1747_, v___f_1745_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1749_, lean_object* v_toPure_1750_, lean_object* v___x_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_toBind_1757_, lean_object* v___y_1758_, lean_object* v___x_1759_, lean_object* v_env_1760_){
_start:
{
uint8_t v___x_469__boxed_1761_; uint8_t v___y_475__boxed_1762_; lean_object* v_res_1763_; 
v___x_469__boxed_1761_ = lean_unbox(v___x_1751_);
v___y_475__boxed_1762_ = lean_unbox(v___y_1758_);
v_res_1763_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1749_, v_toPure_1750_, v___x_469__boxed_1761_, v_inst_1752_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v_inst_1756_, v_toBind_1757_, v___y_475__boxed_1762_, v___x_1759_, v_env_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_n_1769_){
_start:
{
lean_object* v___x_1770_; uint8_t v___y_1772_; uint8_t v___x_1787_; 
v___x_1770_ = l_Lean_KVMap_instValueBool;
v___x_1787_ = l_Lean_isPrivateName(v_n_1769_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = 1;
v___y_1772_ = v___x_1788_;
goto v___jp_1771_;
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = 0;
v___y_1772_ = v___x_1789_;
goto v___jp_1771_;
}
v___jp_1771_:
{
if (v___y_1772_ == 0)
{
lean_object* v_toApplicative_1773_; lean_object* v_toBind_1774_; lean_object* v_toPure_1775_; lean_object* v_getEnv_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___f_1780_; lean_object* v___x_1781_; 
v_toApplicative_1773_ = lean_ctor_get(v_inst_1766_, 0);
v_toBind_1774_ = lean_ctor_get(v_inst_1766_, 1);
lean_inc_n(v_toBind_1774_, 2);
v_toPure_1775_ = lean_ctor_get(v_toApplicative_1773_, 1);
lean_inc(v_toPure_1775_);
v_getEnv_1776_ = lean_ctor_get(v_inst_1767_, 0);
lean_inc(v_getEnv_1776_);
v___x_1777_ = 1;
v___x_1778_ = lean_box(v___x_1777_);
v___x_1779_ = lean_box(v___y_1772_);
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1780_, 0, v_n_1769_);
lean_closure_set(v___f_1780_, 1, v_toPure_1775_);
lean_closure_set(v___f_1780_, 2, v___x_1778_);
lean_closure_set(v___f_1780_, 3, v_inst_1766_);
lean_closure_set(v___f_1780_, 4, v_inst_1767_);
lean_closure_set(v___f_1780_, 5, v_inst_1768_);
lean_closure_set(v___f_1780_, 6, v_inst_1764_);
lean_closure_set(v___f_1780_, 7, v_inst_1765_);
lean_closure_set(v___f_1780_, 8, v_toBind_1774_);
lean_closure_set(v___f_1780_, 9, v___x_1779_);
lean_closure_set(v___f_1780_, 10, v___x_1770_);
v___x_1781_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v_getEnv_1776_, v___f_1780_);
return v___x_1781_;
}
else
{
lean_object* v_toApplicative_1782_; lean_object* v_toPure_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_toApplicative_1782_ = lean_ctor_get(v_inst_1766_, 0);
lean_inc_ref(v_toApplicative_1782_);
lean_dec(v_n_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
lean_dec(v_inst_1765_);
lean_dec_ref(v_inst_1764_);
v_toPure_1783_ = lean_ctor_get(v_toApplicative_1782_, 1);
lean_inc(v_toPure_1783_);
lean_dec_ref(v_toApplicative_1782_);
v___x_1784_ = 0;
v___x_1785_ = lean_box(v___x_1784_);
v___x_1786_ = lean_apply_2(v_toPure_1783_, lean_box(0), v___x_1785_);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_n_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1791_, v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_n_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1798_){
_start:
{
lean_object* v_fst_1799_; uint8_t v___x_1800_; 
v_fst_1799_ = lean_ctor_get(v_x_1798_, 0);
v___x_1800_ = l_Lean_isPrivateName(v_fst_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1801_);
lean_dec_ref(v_x_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1804_, lean_object* v_res_1805_, lean_object* v_____r_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_apply_2(v_toPure_1804_, lean_box(0), v_res_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1808_, lean_object* v_toPure_1809_, lean_object* v_res_1810_, lean_object* v___f_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_toBind_1817_, lean_object* v___f_1818_, lean_object* v_____do__lift_1819_){
_start:
{
if (v_enableLog_1808_ == 0)
{
lean_object* v___x_1820_; 
lean_dec(v___f_1818_);
lean_dec(v_toBind_1817_);
lean_dec(v_inst_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v___f_1811_);
v___x_1820_ = lean_apply_2(v_toPure_1809_, lean_box(0), v_res_1810_);
return v___x_1820_;
}
else
{
uint8_t v_isExporting_1821_; 
v_isExporting_1821_ = lean_ctor_get_uint8(v_____do__lift_1819_, sizeof(void*)*8);
if (v_isExporting_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v___f_1818_);
lean_dec(v_toBind_1817_);
lean_dec(v_inst_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v___f_1811_);
v___x_1822_ = lean_apply_2(v_toPure_1809_, lean_box(0), v_res_1810_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; 
lean_inc(v_res_1810_);
v___x_1823_ = l_List_find_x3f___redArg(v___f_1811_, v_res_1810_);
if (lean_obj_tag(v___x_1823_) == 1)
{
lean_object* v_val_1824_; lean_object* v_fst_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_res_1810_);
lean_dec(v_toPure_1809_);
v_val_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_val_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v_fst_1825_ = lean_ctor_get(v_val_1824_, 0);
lean_inc(v_fst_1825_);
lean_dec(v_val_1824_);
v___x_1826_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v_inst_1816_, v_fst_1825_);
v___x_1827_ = lean_apply_4(v_toBind_1817_, lean_box(0), lean_box(0), v___x_1826_, v___f_1818_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; 
lean_dec(v___x_1823_);
lean_dec(v___f_1818_);
lean_dec(v_toBind_1817_);
lean_dec(v_inst_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec_ref(v_inst_1812_);
v___x_1828_ = lean_apply_2(v_toPure_1809_, lean_box(0), v_res_1810_);
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1829_, lean_object* v_toPure_1830_, lean_object* v_res_1831_, lean_object* v___f_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_toBind_1838_, lean_object* v___f_1839_, lean_object* v_____do__lift_1840_){
_start:
{
uint8_t v_enableLog_boxed_1841_; lean_object* v_res_1842_; 
v_enableLog_boxed_1841_ = lean_unbox(v_enableLog_1829_);
v_res_1842_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1841_, v_toPure_1830_, v_res_1831_, v___f_1832_, v_inst_1833_, v_inst_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_toBind_1838_, v___f_1839_, v_____do__lift_1840_);
lean_dec_ref(v_____do__lift_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1843_, lean_object* v_____do__lift_1844_, lean_object* v_____do__lift_1845_, lean_object* v_id_1846_, lean_object* v_toPure_1847_, uint8_t v_enableLog_1848_, lean_object* v___f_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_toBind_1855_, lean_object* v_getEnv_1856_, lean_object* v_____do__lift_1857_){
_start:
{
lean_object* v_res_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; 
v_res_1858_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1843_, v_____do__lift_1844_, v_____do__lift_1845_, v_____do__lift_1857_, v_id_1846_);
lean_inc(v_res_1858_);
lean_inc(v_toPure_1847_);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1859_, 0, v_toPure_1847_);
lean_closure_set(v___f_1859_, 1, v_res_1858_);
v___x_1860_ = lean_box(v_enableLog_1848_);
lean_inc(v_toBind_1855_);
v___f_1861_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1861_, 0, v___x_1860_);
lean_closure_set(v___f_1861_, 1, v_toPure_1847_);
lean_closure_set(v___f_1861_, 2, v_res_1858_);
lean_closure_set(v___f_1861_, 3, v___f_1849_);
lean_closure_set(v___f_1861_, 4, v_inst_1850_);
lean_closure_set(v___f_1861_, 5, v_inst_1851_);
lean_closure_set(v___f_1861_, 6, v_inst_1852_);
lean_closure_set(v___f_1861_, 7, v_inst_1853_);
lean_closure_set(v___f_1861_, 8, v_inst_1854_);
lean_closure_set(v___f_1861_, 9, v_toBind_1855_);
lean_closure_set(v___f_1861_, 10, v___f_1859_);
v___x_1862_ = lean_apply_4(v_toBind_1855_, lean_box(0), lean_box(0), v_getEnv_1856_, v___f_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1863_, lean_object* v_____do__lift_1864_, lean_object* v_____do__lift_1865_, lean_object* v_id_1866_, lean_object* v_toPure_1867_, lean_object* v_enableLog_1868_, lean_object* v___f_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_toBind_1875_, lean_object* v_getEnv_1876_, lean_object* v_____do__lift_1877_){
_start:
{
uint8_t v_enableLog_boxed_1878_; lean_object* v_res_1879_; 
v_enableLog_boxed_1878_ = lean_unbox(v_enableLog_1868_);
v_res_1879_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1863_, v_____do__lift_1864_, v_____do__lift_1865_, v_id_1866_, v_toPure_1867_, v_enableLog_boxed_1878_, v___f_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_toBind_1875_, v_getEnv_1876_, v_____do__lift_1877_);
lean_dec_ref(v_____do__lift_1864_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1880_, lean_object* v_____do__lift_1881_, lean_object* v_id_1882_, lean_object* v_toPure_1883_, uint8_t v_enableLog_1884_, lean_object* v___f_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_toBind_1891_, lean_object* v_getEnv_1892_, lean_object* v_getOpenDecls_1893_, lean_object* v_____do__lift_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_box(v_enableLog_1884_);
lean_inc(v_toBind_1891_);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1896_, 0, v_____do__lift_1880_);
lean_closure_set(v___f_1896_, 1, v_____do__lift_1881_);
lean_closure_set(v___f_1896_, 2, v_____do__lift_1894_);
lean_closure_set(v___f_1896_, 3, v_id_1882_);
lean_closure_set(v___f_1896_, 4, v_toPure_1883_);
lean_closure_set(v___f_1896_, 5, v___x_1895_);
lean_closure_set(v___f_1896_, 6, v___f_1885_);
lean_closure_set(v___f_1896_, 7, v_inst_1886_);
lean_closure_set(v___f_1896_, 8, v_inst_1887_);
lean_closure_set(v___f_1896_, 9, v_inst_1888_);
lean_closure_set(v___f_1896_, 10, v_inst_1889_);
lean_closure_set(v___f_1896_, 11, v_inst_1890_);
lean_closure_set(v___f_1896_, 12, v_toBind_1891_);
lean_closure_set(v___f_1896_, 13, v_getEnv_1892_);
v___x_1897_ = lean_apply_4(v_toBind_1891_, lean_box(0), lean_box(0), v_getOpenDecls_1893_, v___f_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1898_, lean_object* v_____do__lift_1899_, lean_object* v_id_1900_, lean_object* v_toPure_1901_, lean_object* v_enableLog_1902_, lean_object* v___f_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_toBind_1909_, lean_object* v_getEnv_1910_, lean_object* v_getOpenDecls_1911_, lean_object* v_____do__lift_1912_){
_start:
{
uint8_t v_enableLog_boxed_1913_; lean_object* v_res_1914_; 
v_enableLog_boxed_1913_ = lean_unbox(v_enableLog_1902_);
v_res_1914_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1898_, v_____do__lift_1899_, v_id_1900_, v_toPure_1901_, v_enableLog_boxed_1913_, v___f_1903_, v_inst_1904_, v_inst_1905_, v_inst_1906_, v_inst_1907_, v_inst_1908_, v_toBind_1909_, v_getEnv_1910_, v_getOpenDecls_1911_, v_____do__lift_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1915_, lean_object* v_____do__lift_1916_, lean_object* v_id_1917_, lean_object* v_toPure_1918_, uint8_t v_enableLog_1919_, lean_object* v___f_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_toBind_1926_, lean_object* v_getEnv_1927_, lean_object* v_____do__lift_1928_){
_start:
{
lean_object* v_getCurrNamespace_1929_; lean_object* v_getOpenDecls_1930_; lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v_getCurrNamespace_1929_ = lean_ctor_get(v_inst_1915_, 0);
lean_inc(v_getCurrNamespace_1929_);
v_getOpenDecls_1930_ = lean_ctor_get(v_inst_1915_, 1);
lean_inc(v_getOpenDecls_1930_);
lean_dec_ref(v_inst_1915_);
v___x_1931_ = lean_box(v_enableLog_1919_);
lean_inc(v_toBind_1926_);
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1932_, 0, v_____do__lift_1916_);
lean_closure_set(v___f_1932_, 1, v_____do__lift_1928_);
lean_closure_set(v___f_1932_, 2, v_id_1917_);
lean_closure_set(v___f_1932_, 3, v_toPure_1918_);
lean_closure_set(v___f_1932_, 4, v___x_1931_);
lean_closure_set(v___f_1932_, 5, v___f_1920_);
lean_closure_set(v___f_1932_, 6, v_inst_1921_);
lean_closure_set(v___f_1932_, 7, v_inst_1922_);
lean_closure_set(v___f_1932_, 8, v_inst_1923_);
lean_closure_set(v___f_1932_, 9, v_inst_1924_);
lean_closure_set(v___f_1932_, 10, v_inst_1925_);
lean_closure_set(v___f_1932_, 11, v_toBind_1926_);
lean_closure_set(v___f_1932_, 12, v_getEnv_1927_);
lean_closure_set(v___f_1932_, 13, v_getOpenDecls_1930_);
v___x_1933_ = lean_apply_4(v_toBind_1926_, lean_box(0), lean_box(0), v_getCurrNamespace_1929_, v___f_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1934_, lean_object* v_____do__lift_1935_, lean_object* v_id_1936_, lean_object* v_toPure_1937_, lean_object* v_enableLog_1938_, lean_object* v___f_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_toBind_1945_, lean_object* v_getEnv_1946_, lean_object* v_____do__lift_1947_){
_start:
{
uint8_t v_enableLog_boxed_1948_; lean_object* v_res_1949_; 
v_enableLog_boxed_1948_ = lean_unbox(v_enableLog_1938_);
v_res_1949_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1934_, v_____do__lift_1935_, v_id_1936_, v_toPure_1937_, v_enableLog_boxed_1948_, v___f_1939_, v_inst_1940_, v_inst_1941_, v_inst_1942_, v_inst_1943_, v_inst_1944_, v_toBind_1945_, v_getEnv_1946_, v_____do__lift_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_id_1952_, lean_object* v_toPure_1953_, uint8_t v_enableLog_1954_, lean_object* v___f_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_toBind_1960_, lean_object* v_getEnv_1961_, lean_object* v_____do__lift_1962_){
_start:
{
lean_object* v_getOptions_1963_; lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; 
v_getOptions_1963_ = lean_ctor_get(v_inst_1950_, 0);
lean_inc(v_getOptions_1963_);
v___x_1964_ = lean_box(v_enableLog_1954_);
lean_inc(v_toBind_1960_);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1965_, 0, v_inst_1951_);
lean_closure_set(v___f_1965_, 1, v_____do__lift_1962_);
lean_closure_set(v___f_1965_, 2, v_id_1952_);
lean_closure_set(v___f_1965_, 3, v_toPure_1953_);
lean_closure_set(v___f_1965_, 4, v___x_1964_);
lean_closure_set(v___f_1965_, 5, v___f_1955_);
lean_closure_set(v___f_1965_, 6, v_inst_1956_);
lean_closure_set(v___f_1965_, 7, v_inst_1957_);
lean_closure_set(v___f_1965_, 8, v_inst_1950_);
lean_closure_set(v___f_1965_, 9, v_inst_1958_);
lean_closure_set(v___f_1965_, 10, v_inst_1959_);
lean_closure_set(v___f_1965_, 11, v_toBind_1960_);
lean_closure_set(v___f_1965_, 12, v_getEnv_1961_);
v___x_1966_ = lean_apply_4(v_toBind_1960_, lean_box(0), lean_box(0), v_getOptions_1963_, v___f_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_id_1969_, lean_object* v_toPure_1970_, lean_object* v_enableLog_1971_, lean_object* v___f_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_toBind_1977_, lean_object* v_getEnv_1978_, lean_object* v_____do__lift_1979_){
_start:
{
uint8_t v_enableLog_boxed_1980_; lean_object* v_res_1981_; 
v_enableLog_boxed_1980_ = lean_unbox(v_enableLog_1971_);
v_res_1981_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1967_, v_inst_1968_, v_id_1969_, v_toPure_1970_, v_enableLog_boxed_1980_, v___f_1972_, v_inst_1973_, v_inst_1974_, v_inst_1975_, v_inst_1976_, v_toBind_1977_, v_getEnv_1978_, v_____do__lift_1979_);
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
lean_closure_set(v___f_1997_, 0, v_inst_1986_);
lean_closure_set(v___f_1997_, 1, v_inst_1984_);
lean_closure_set(v___f_1997_, 2, v_id_1989_);
lean_closure_set(v___f_1997_, 3, v_toPure_1994_);
lean_closure_set(v___f_1997_, 4, v___x_1996_);
lean_closure_set(v___f_1997_, 5, v___f_1995_);
lean_closure_set(v___f_1997_, 6, v_inst_1983_);
lean_closure_set(v___f_1997_, 7, v_inst_1985_);
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
lean_dec_ref_known(v_x_2187_, 4);
lean_dec(v_toBind_2189_);
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
lean_dec(v_toBind_2447_);
lean_dec_ref_known(v_stx_2444_, 4);
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
lean_inc_ref(v_inst_2605_);
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
lean_dec_ref(v_inst_2605_);
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
lean_dec_ref(v_inst_2605_);
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
lean_inc(v_name_2783_);
v___x_2784_ = l_Lean_privateToUserName_x3f(v_name_2783_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_inc(v_name_2783_);
v___y_2762_ = v_name_2783_;
goto v___jp_2761_;
}
else
{
lean_object* v_val_2785_; 
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
uint8_t v_____do__lift_1060__boxed_2933_; lean_object* v_res_2934_; 
v_____do__lift_1060__boxed_2933_ = lean_unbox(v_____do__lift_2932_);
v_res_2934_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2931_, v_____do__lift_1060__boxed_2933_);
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
lean_inc_ref_n(v___x_3037_, 2);
v___x_3053_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_3037_, v_inst_3020_);
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
lean_dec_ref(v_inst_3210_);
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
lean_dec_ref(v_inst_3314_);
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
lean_dec_ref(v_inst_3330_);
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
lean_dec_ref(v_inst_3390_);
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
lean_inc_ref(v_inst_3405_);
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
lean_inc_ref(v_inst_3405_);
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
lean_inc_ref(v_inst_3551_);
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
