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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
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
v___x_125_ = l_Array_instInhabited___redArg();
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
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_1075__boxed_285_; size_t v_x_1076__boxed_286_; lean_object* v_res_287_; 
v_x_1075__boxed_285_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_x_1076__boxed_286_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_res_287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_280_, v_x_1075__boxed_285_, v_x_1076__boxed_286_, v_x_283_, v_x_284_);
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
size_t v_x_1579__boxed_535_; lean_object* v_res_536_; 
v_x_1579__boxed_535_ = lean_unbox_usize(v_x_533_);
lean_dec(v_x_533_);
v_res_536_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_532_, v_x_1579__boxed_535_, v_x_534_);
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
size_t v_x_1744__boxed_639_; lean_object* v_res_640_; 
v_x_1744__boxed_639_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_640_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_635_, v_x_636_, v_x_1744__boxed_639_, v_x_638_);
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
size_t v_x_1760__boxed_662_; size_t v_x_1761__boxed_663_; lean_object* v_res_664_; 
v_x_1760__boxed_662_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_x_1761__boxed_663_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_664_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_656_, v_x_657_, v_x_1760__boxed_662_, v_x_1761__boxed_663_, v_x_660_, v_x_661_);
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
v___x_808_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
static lean_object* _init_l_Lean_getAliasState___closed__0(void){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_SMap_instInhabited___redArg();
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_851_){
_start:
{
lean_object* v___x_852_; lean_object* v_toEnvExtension_853_; lean_object* v_asyncMode_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_852_ = l_Lean_aliasExtension;
v_toEnvExtension_853_ = lean_ctor_get(v___x_852_, 0);
v_asyncMode_854_ = lean_ctor_get(v_toEnvExtension_853_, 2);
v___x_855_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_856_ = lean_box(0);
v___x_857_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_855_, v___x_852_, v_env_851_, v_asyncMode_854_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_858_, uint8_t v_skipProtected_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v_env_858_);
v___x_862_ = l_List_reverse___redArg(v_a_861_);
return v___x_862_;
}
else
{
lean_object* v_head_863_; lean_object* v_tail_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_875_; 
v_head_863_ = lean_ctor_get(v_a_860_, 0);
v_tail_864_ = lean_ctor_get(v_a_860_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_875_ == 0)
{
v___x_866_ = v_a_860_;
v_isShared_867_ = v_isSharedCheck_875_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_tail_864_);
lean_inc(v_head_863_);
lean_dec(v_a_860_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_875_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; 
lean_inc(v_head_863_);
lean_inc_ref(v_env_858_);
v___x_868_ = l_Lean_isProtected(v_env_858_, v_head_863_);
if (v___x_868_ == 0)
{
if (v_skipProtected_859_ == 0)
{
lean_del_object(v___x_866_);
lean_dec(v_head_863_);
v_a_860_ = v_tail_864_;
goto _start;
}
else
{
lean_object* v___x_871_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_a_861_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_head_863_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_a_861_);
v___x_871_ = v_reuseFailAlloc_873_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_a_860_ = v_tail_864_;
v_a_861_ = v___x_871_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_866_);
lean_dec(v_head_863_);
v_a_860_ = v_tail_864_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_876_, lean_object* v_skipProtected_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
uint8_t v_skipProtected_boxed_880_; lean_object* v_res_881_; 
v_skipProtected_boxed_880_ = lean_unbox(v_skipProtected_877_);
v_res_881_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_876_, v_skipProtected_boxed_880_, v_a_878_, v_a_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_882_, lean_object* v_a_883_, uint8_t v_skipProtected_884_){
_start:
{
lean_object* v___x_885_; lean_object* v_toEnvExtension_886_; lean_object* v_asyncMode_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_885_ = l_Lean_aliasExtension;
v_toEnvExtension_886_ = lean_ctor_get(v___x_885_, 0);
v_asyncMode_887_ = lean_ctor_get(v_toEnvExtension_886_, 2);
v___x_888_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_889_ = lean_box(0);
lean_inc_ref(v_env_882_);
v___x_890_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_888_, v___x_885_, v_env_882_, v_asyncMode_887_, v___x_889_);
v___x_891_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_890_, v_a_883_);
lean_dec(v___x_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_892_; 
lean_dec_ref(v_env_882_);
v___x_892_ = lean_box(0);
return v___x_892_;
}
else
{
if (v_skipProtected_884_ == 0)
{
lean_object* v_val_893_; 
lean_dec_ref(v_env_882_);
v_val_893_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v___x_891_, 1);
return v_val_893_;
}
else
{
lean_object* v_val_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_val_894_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v___x_891_, 1);
v___x_895_ = lean_box(0);
v___x_896_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_882_, v_skipProtected_884_, v_val_894_, v___x_895_);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_897_, lean_object* v_a_898_, lean_object* v_skipProtected_899_){
_start:
{
uint8_t v_skipProtected_boxed_900_; lean_object* v_res_901_; 
v_skipProtected_boxed_900_ = lean_unbox(v_skipProtected_899_);
v_res_901_ = l_Lean_getAliases(v_env_897_, v_a_898_, v_skipProtected_boxed_900_);
lean_dec(v_a_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_902_, lean_object* v_as_903_, lean_object* v_a_904_, lean_object* v_es_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_902_, v_es_905_);
if (v___x_906_ == 0)
{
lean_dec(v_a_904_);
return v_as_903_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_907_, 0, v_a_904_);
lean_ctor_set(v___x_907_, 1, v_as_903_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_908_, lean_object* v_as_909_, lean_object* v_a_910_, lean_object* v_es_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_getRevAliases___lam__0(v_e_908_, v_as_909_, v_a_910_, v_es_911_);
lean_dec(v_es_911_);
lean_dec(v_e_908_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_913_, lean_object* v_keys_914_, lean_object* v_vals_915_, lean_object* v_i_916_, lean_object* v_acc_917_){
_start:
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_array_get_size(v_keys_914_);
v___x_919_ = lean_nat_dec_lt(v_i_916_, v___x_918_);
if (v___x_919_ == 0)
{
lean_dec(v_i_916_);
lean_dec(v_f_913_);
return v_acc_917_;
}
else
{
lean_object* v_k_920_; lean_object* v_v_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_k_920_ = lean_array_fget_borrowed(v_keys_914_, v_i_916_);
v_v_921_ = lean_array_fget_borrowed(v_vals_915_, v_i_916_);
lean_inc(v_f_913_);
lean_inc(v_v_921_);
lean_inc(v_k_920_);
v___x_922_ = lean_apply_3(v_f_913_, v_acc_917_, v_k_920_, v_v_921_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_add(v_i_916_, v___x_923_);
lean_dec(v_i_916_);
v_i_916_ = v___x_924_;
v_acc_917_ = v___x_922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_926_, lean_object* v_keys_927_, lean_object* v_vals_928_, lean_object* v_i_929_, lean_object* v_acc_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_926_, v_keys_927_, v_vals_928_, v_i_929_, v_acc_930_);
lean_dec_ref(v_vals_928_);
lean_dec_ref(v_keys_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_932_, lean_object* v_as_933_, size_t v_i_934_, size_t v_stop_935_, lean_object* v_b_936_){
_start:
{
lean_object* v___y_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_eq(v_i_934_, v_stop_935_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_array_uget_borrowed(v_as_933_, v_i_934_);
switch(lean_obj_tag(v___x_943_))
{
case 0:
{
lean_object* v_key_944_; lean_object* v_val_945_; lean_object* v___x_946_; 
v_key_944_ = lean_ctor_get(v___x_943_, 0);
v_val_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_f_932_);
lean_inc(v_val_945_);
lean_inc(v_key_944_);
v___x_946_ = lean_apply_3(v_f_932_, v_b_936_, v_key_944_, v_val_945_);
v___y_938_ = v___x_946_;
goto v___jp_937_;
}
case 1:
{
lean_object* v_node_947_; lean_object* v___x_948_; 
v_node_947_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_f_932_);
v___x_948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_932_, v_node_947_, v_b_936_);
v___y_938_ = v___x_948_;
goto v___jp_937_;
}
default: 
{
v___y_938_ = v_b_936_;
goto v___jp_937_;
}
}
}
else
{
lean_dec(v_f_932_);
return v_b_936_;
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_934_, v___x_939_);
v_i_934_ = v___x_940_;
v_b_936_ = v___y_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_950_) == 0)
{
lean_object* v_es_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v_es_952_ = lean_ctor_get(v_x_950_, 0);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_array_get_size(v_es_952_);
v___x_955_ = lean_nat_dec_lt(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
lean_dec(v_f_949_);
return v_x_951_;
}
else
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_954_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_949_, v_es_952_, v___x_956_, v___x_957_, v_x_951_);
return v___x_958_;
}
}
else
{
lean_object* v_ks_959_; lean_object* v_vs_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_ks_959_ = lean_ctor_get(v_x_950_, 0);
v_vs_960_ = lean_ctor_get(v_x_950_, 1);
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_949_, v_ks_959_, v_vs_960_, v___x_961_, v_x_951_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_963_, v_x_964_, v_x_965_);
lean_dec_ref(v_x_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_967_, lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_stop_970_, lean_object* v_b_971_){
_start:
{
size_t v_i_boxed_972_; size_t v_stop_boxed_973_; lean_object* v_res_974_; 
v_i_boxed_972_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_973_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_967_, v_as_968_, v_i_boxed_972_, v_stop_boxed_973_, v_b_971_);
lean_dec_ref(v_as_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_975_, lean_object* v_x1_976_, lean_object* v_x2_977_, lean_object* v_x3_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_apply_3(v_f_975_, v_x1_976_, v_x2_977_, v_x3_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_980_, lean_object* v_f_981_, lean_object* v_init_982_){
_start:
{
lean_object* v___f_983_; lean_object* v___x_984_; 
v___f_983_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_983_, 0, v_f_981_);
v___x_984_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_983_, v_map_980_, v_init_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_985_, lean_object* v_f_986_, lean_object* v_init_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_985_, v_f_986_, v_init_987_);
lean_dec_ref(v_map_985_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_dec(v_f_989_);
return v_x_990_;
}
else
{
lean_object* v_key_992_; lean_object* v_value_993_; lean_object* v_tail_994_; lean_object* v___x_995_; 
v_key_992_ = lean_ctor_get(v_x_991_, 0);
lean_inc(v_key_992_);
v_value_993_ = lean_ctor_get(v_x_991_, 1);
lean_inc(v_value_993_);
v_tail_994_ = lean_ctor_get(v_x_991_, 2);
lean_inc(v_tail_994_);
lean_dec_ref_known(v_x_991_, 3);
lean_inc(v_f_989_);
v___x_995_ = lean_apply_3(v_f_989_, v_x_990_, v_key_992_, v_value_993_);
v_x_990_ = v___x_995_;
v_x_991_ = v_tail_994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_997_, lean_object* v_as_998_, size_t v_i_999_, size_t v_stop_1000_, lean_object* v_b_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_eq(v_i_999_, v_stop_1000_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; size_t v___x_1005_; size_t v___x_1006_; 
v___x_1003_ = lean_array_uget_borrowed(v_as_998_, v_i_999_);
lean_inc(v___x_1003_);
lean_inc(v_f_997_);
v___x_1004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_997_, v_b_1001_, v___x_1003_);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_999_, v___x_1005_);
v_i_999_ = v___x_1006_;
v_b_1001_ = v___x_1004_;
goto _start;
}
else
{
lean_dec(v_f_997_);
return v_b_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1008_, lean_object* v_as_1009_, lean_object* v_i_1010_, lean_object* v_stop_1011_, lean_object* v_b_1012_){
_start:
{
size_t v_i_boxed_1013_; size_t v_stop_boxed_1014_; lean_object* v_res_1015_; 
v_i_boxed_1013_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_stop_boxed_1014_ = lean_unbox_usize(v_stop_1011_);
lean_dec(v_stop_1011_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1008_, v_as_1009_, v_i_boxed_1013_, v_stop_boxed_1014_, v_b_1012_);
lean_dec_ref(v_as_1009_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1016_, lean_object* v_init_1017_, lean_object* v_m_1018_){
_start:
{
lean_object* v_map_u2081_1019_; lean_object* v_map_u2082_1020_; lean_object* v_buckets_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_map_u2081_1019_ = lean_ctor_get(v_m_1018_, 0);
v_map_u2082_1020_ = lean_ctor_get(v_m_1018_, 1);
v_buckets_1021_ = lean_ctor_get(v_map_u2081_1019_, 1);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_array_get_size(v_buckets_1021_);
v___x_1024_ = lean_nat_dec_lt(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1020_, v_f_1016_, v_init_1017_);
return v___x_1025_;
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1023_);
lean_inc(v_f_1016_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1016_, v_buckets_1021_, v___x_1026_, v___x_1027_, v_init_1017_);
v___x_1029_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1020_, v_f_1016_, v___x_1028_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1030_, lean_object* v_init_1031_, lean_object* v_m_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1030_, v_init_1031_, v_m_1032_);
lean_dec_ref(v_m_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1034_, lean_object* v_e_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v_toEnvExtension_1037_; lean_object* v_asyncMode_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1036_ = l_Lean_aliasExtension;
v_toEnvExtension_1037_ = lean_ctor_get(v___x_1036_, 0);
v_asyncMode_1038_ = lean_ctor_get(v_toEnvExtension_1037_, 2);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1039_, 0, v_e_1035_);
v___x_1040_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1040_, v___x_1036_, v_env_1034_, v_asyncMode_1038_, v___x_1042_);
v___x_1044_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1039_, v___x_1041_, v___x_1043_);
lean_dec(v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1045_, lean_object* v_00_u03c3_1046_, lean_object* v_f_1047_, lean_object* v_init_1048_, lean_object* v_m_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1047_, v_init_1048_, v_m_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_00_u03c3_1052_, lean_object* v_f_1053_, lean_object* v_init_1054_, lean_object* v_m_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1051_, v_00_u03c3_1052_, v_f_1053_, v_init_1054_, v_m_1055_);
lean_dec_ref(v_m_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1057_, lean_object* v_00_u03c3_1058_, lean_object* v_f_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1059_, v_x_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_map_1065_, lean_object* v_f_1066_, lean_object* v_init_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1065_, v_f_1066_, v_init_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_map_1071_, lean_object* v_f_1072_, lean_object* v_init_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1069_, v_00_u03b2_1070_, v_map_1071_, v_f_1072_, v_init_1073_);
lean_dec_ref(v_map_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1075_, lean_object* v_00_u03c3_1076_, lean_object* v_f_1077_, lean_object* v_as_1078_, size_t v_i_1079_, size_t v_stop_1080_, lean_object* v_b_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1077_, v_as_1078_, v_i_1079_, v_stop_1080_, v_b_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_00_u03c3_1084_, lean_object* v_f_1085_, lean_object* v_as_1086_, lean_object* v_i_1087_, lean_object* v_stop_1088_, lean_object* v_b_1089_){
_start:
{
size_t v_i_boxed_1090_; size_t v_stop_boxed_1091_; lean_object* v_res_1092_; 
v_i_boxed_1090_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_stop_boxed_1091_ = lean_unbox_usize(v_stop_1088_);
lean_dec(v_stop_1088_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1083_, v_00_u03c3_1084_, v_f_1085_, v_as_1086_, v_i_boxed_1090_, v_stop_boxed_1091_, v_b_1089_);
lean_dec_ref(v_as_1086_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1093_, lean_object* v_f_1094_, lean_object* v_init_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1094_, v_map_1093_, v_init_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1097_, lean_object* v_f_1098_, lean_object* v_init_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1097_, v_f_1098_, v_init_1099_);
lean_dec_ref(v_map_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_map_1103_, lean_object* v_f_1104_, lean_object* v_init_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1104_, v_map_1103_, v_init_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_map_1109_, lean_object* v_f_1110_, lean_object* v_init_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1107_, v_00_u03b2_1108_, v_map_1109_, v_f_1110_, v_init_1111_);
lean_dec_ref(v_map_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1113_, lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_f_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1116_, v_x_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1120_, lean_object* v_00_u03b1_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_f_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1120_, v_00_u03b1_1121_, v_00_u03b2_1122_, v_f_1123_, v_x_1124_, v_x_1125_);
lean_dec_ref(v_x_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_00_u03c3_1129_, lean_object* v_f_1130_, lean_object* v_as_1131_, size_t v_i_1132_, size_t v_stop_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1130_, v_as_1131_, v_i_1132_, v_stop_1133_, v_b_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_00_u03c3_1138_, lean_object* v_f_1139_, lean_object* v_as_1140_, lean_object* v_i_1141_, lean_object* v_stop_1142_, lean_object* v_b_1143_){
_start:
{
size_t v_i_boxed_1144_; size_t v_stop_boxed_1145_; lean_object* v_res_1146_; 
v_i_boxed_1144_ = lean_unbox_usize(v_i_1141_);
lean_dec(v_i_1141_);
v_stop_boxed_1145_ = lean_unbox_usize(v_stop_1142_);
lean_dec(v_stop_1142_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1136_, v_00_u03b2_1137_, v_00_u03c3_1138_, v_f_1139_, v_as_1140_, v_i_boxed_1144_, v_stop_boxed_1145_, v_b_1143_);
lean_dec_ref(v_as_1140_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1147_, lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_f_1150_, lean_object* v_keys_1151_, lean_object* v_vals_1152_, lean_object* v_heq_1153_, lean_object* v_i_1154_, lean_object* v_acc_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1150_, v_keys_1151_, v_vals_1152_, v_i_1154_, v_acc_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1157_, lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_f_1160_, lean_object* v_keys_1161_, lean_object* v_vals_1162_, lean_object* v_heq_1163_, lean_object* v_i_1164_, lean_object* v_acc_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1157_, v_00_u03b1_1158_, v_00_u03b2_1159_, v_f_1160_, v_keys_1161_, v_vals_1162_, v_heq_1163_, v_i_1164_, v_acc_1165_);
lean_dec_ref(v_vals_1162_);
lean_dec_ref(v_keys_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1167_, lean_object* v_declName_1168_){
_start:
{
uint8_t v___y_1170_; uint8_t v___x_1173_; 
v___x_1173_ = l_Lean_Environment_containsOnBranch(v_env_1167_, v_declName_1168_);
if (v___x_1173_ == 0)
{
uint8_t v___x_1174_; 
lean_inc(v_declName_1168_);
lean_inc_ref(v_env_1167_);
v___x_1174_ = lean_is_reserved_name(v_env_1167_, v_declName_1168_);
v___y_1170_ = v___x_1174_;
goto v___jp_1169_;
}
else
{
v___y_1170_ = v___x_1173_;
goto v___jp_1169_;
}
v___jp_1169_:
{
if (v___y_1170_ == 0)
{
uint8_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 1;
v___x_1172_ = l_Lean_Environment_contains(v_env_1167_, v_declName_1168_, v___x_1171_);
return v___x_1172_;
}
else
{
lean_dec(v_declName_1168_);
lean_dec_ref(v_env_1167_);
return v___y_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1175_, lean_object* v_declName_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1175_, v_declName_1176_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1179_, lean_object* v_decl_1180_, lean_object* v_ref_1181_){
_start:
{
lean_object* v_defValue_1183_; lean_object* v_descr_1184_; lean_object* v_deprecation_x3f_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_defValue_1183_ = lean_ctor_get(v_decl_1180_, 0);
v_descr_1184_ = lean_ctor_get(v_decl_1180_, 1);
v_deprecation_x3f_1185_ = lean_ctor_get(v_decl_1180_, 2);
v___x_1186_ = lean_alloc_ctor(1, 0, 1);
v___x_1187_ = lean_unbox(v_defValue_1183_);
lean_ctor_set_uint8(v___x_1186_, 0, v___x_1187_);
lean_inc(v_deprecation_x3f_1185_);
lean_inc_ref(v_descr_1184_);
lean_inc_n(v_name_1179_, 2);
v___x_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1188_, 0, v_name_1179_);
lean_ctor_set(v___x_1188_, 1, v_ref_1181_);
lean_ctor_set(v___x_1188_, 2, v___x_1186_);
lean_ctor_set(v___x_1188_, 3, v_descr_1184_);
lean_ctor_set(v___x_1188_, 4, v_deprecation_x3f_1185_);
v___x_1189_ = lean_register_option(v_name_1179_, v___x_1188_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1197_; 
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1189_, 0);
lean_dec(v_unused_1198_);
v___x_1191_ = v___x_1189_;
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v___x_1189_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_inc(v_defValue_1183_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_name_1179_);
lean_ctor_set(v___x_1193_, 1, v_defValue_1183_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1193_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_name_1179_);
v_a_1199_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1189_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1189_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1207_, lean_object* v_decl_1208_, lean_object* v_ref_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1207_, v_decl_1208_, v_ref_1209_);
lean_dec_ref(v_decl_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1231_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1232_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1233_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1230_, v___x_1231_, v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1255_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1256_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1257_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1254_, v___x_1255_, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1260_, lean_object* v_opt_1261_){
_start:
{
lean_object* v_name_1262_; lean_object* v_defValue_1263_; lean_object* v_map_1264_; lean_object* v___x_1265_; 
v_name_1262_ = lean_ctor_get(v_opt_1261_, 0);
v_defValue_1263_ = lean_ctor_get(v_opt_1261_, 1);
v_map_1264_ = lean_ctor_get(v_opts_1260_, 0);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1264_, v_name_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_defValue_1263_);
return v___x_1266_;
}
else
{
lean_object* v_val_1267_; 
v_val_1267_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v___x_1265_, 1);
if (lean_obj_tag(v_val_1267_) == 1)
{
uint8_t v_v_1268_; 
v_v_1268_ = lean_ctor_get_uint8(v_val_1267_, 0);
lean_dec_ref_known(v_val_1267_, 0);
return v_v_1268_;
}
else
{
uint8_t v___x_1269_; 
lean_dec(v_val_1267_);
v___x_1269_ = lean_unbox(v_defValue_1263_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1270_, lean_object* v_opt_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1270_, v_opt_1271_);
lean_dec_ref(v_opt_1271_);
lean_dec_ref(v_opts_1270_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1277_, lean_object* v_env_1278_, lean_object* v_as_1279_, size_t v_sz_1280_, size_t v_i_1281_, lean_object* v_b_1282_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_usize_dec_lt(v_i_1281_, v_sz_1280_);
if (v___x_1283_ == 0)
{
lean_dec_ref(v_env_1278_);
lean_dec(v_declName_1277_);
lean_inc_ref(v_b_1282_);
return v_b_1282_;
}
else
{
lean_object* v_a_1284_; lean_object* v_toImport_1285_; lean_object* v_module_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_a_1284_ = lean_array_uget_borrowed(v_as_1279_, v_i_1281_);
v_toImport_1285_ = lean_ctor_get(v_a_1284_, 0);
v_module_1286_ = lean_ctor_get(v_toImport_1285_, 0);
v___x_1287_ = lean_box(0);
lean_inc(v_declName_1277_);
lean_inc(v_module_1286_);
v___x_1288_ = l_Lean_mkPrivateNameCore(v_module_1286_, v_declName_1277_);
lean_inc(v___x_1288_);
lean_inc_ref(v_env_1278_);
v___x_1289_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1278_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; 
lean_dec(v___x_1288_);
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1281_, v___x_1291_);
v_i_1281_ = v___x_1292_;
v_b_1282_ = v___x_1290_;
goto _start;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v_env_1278_);
lean_dec(v_declName_1277_);
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1288_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1287_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1297_, lean_object* v_env_1298_, lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_){
_start:
{
size_t v_sz_boxed_1303_; size_t v_i_boxed_1304_; lean_object* v_res_1305_; 
v_sz_boxed_1303_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1304_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1297_, v_env_1298_, v_as_1299_, v_sz_boxed_1303_, v_i_boxed_1304_, v_b_1302_);
lean_dec_ref(v_b_1302_);
lean_dec_ref(v_as_1299_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1306_, lean_object* v_opts_1307_, lean_object* v_declName_1308_){
_start:
{
uint8_t v_isExporting_1324_; 
v_isExporting_1324_ = lean_ctor_get_uint8(v_env_1306_, sizeof(void*)*8);
if (v_isExporting_1324_ == 0)
{
goto v___jp_1309_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1326_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1307_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec(v_declName_1308_);
lean_dec_ref(v_env_1306_);
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
else
{
goto v___jp_1309_;
}
}
v___jp_1309_:
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
lean_inc(v_declName_1308_);
v___x_1310_ = l_Lean_mkPrivateName(v_env_1306_, v_declName_1308_);
lean_inc(v___x_1310_);
lean_inc_ref(v_env_1306_);
v___x_1311_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1306_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; uint8_t v_isModule_1313_; 
lean_dec(v___x_1310_);
v___x_1312_ = l_Lean_Environment_header(v_env_1306_);
v_isModule_1313_ = lean_ctor_get_uint8(v___x_1312_, sizeof(void*)*7 + 4);
if (v_isModule_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v___x_1312_);
lean_dec(v_declName_1308_);
lean_dec_ref(v_env_1306_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
lean_object* v_importAllModules_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; size_t v_sz_1318_; size_t v___x_1319_; lean_object* v___x_1320_; lean_object* v_fst_1321_; 
v_importAllModules_1315_ = lean_ctor_get(v___x_1312_, 5);
lean_inc_ref(v_importAllModules_1315_);
lean_dec_ref(v___x_1312_);
v___x_1316_ = lean_box(0);
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1318_ = lean_array_size(v_importAllModules_1315_);
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1308_, v_env_1306_, v_importAllModules_1315_, v_sz_1318_, v___x_1319_, v___x_1317_);
lean_dec_ref(v_importAllModules_1315_);
v_fst_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_fst_1321_);
lean_dec_ref(v___x_1320_);
if (lean_obj_tag(v_fst_1321_) == 0)
{
return v___x_1316_;
}
else
{
lean_object* v_val_1322_; 
v_val_1322_ = lean_ctor_get(v_fst_1321_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_fst_1321_, 1);
return v_val_1322_;
}
}
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_declName_1308_);
lean_dec_ref(v_env_1306_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1310_);
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1328_, lean_object* v_opts_1329_, lean_object* v_declName_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1328_, v_opts_1329_, v_declName_1330_);
lean_dec_ref(v_opts_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1332_, lean_object* v_opts_1333_, lean_object* v_ns_1334_, lean_object* v_id_1335_){
_start:
{
lean_object* v_resolvedId_1336_; uint8_t v___x_1337_; lean_object* v_resolvedIds_1338_; 
lean_inc(v_id_1335_);
v_resolvedId_1336_ = l_Lean_Name_append(v_ns_1334_, v_id_1335_);
v___x_1337_ = l_Lean_Name_isAtomic(v_id_1335_);
lean_dec(v_id_1335_);
lean_inc_ref(v_env_1332_);
v_resolvedIds_1338_ = l_Lean_getAliases(v_env_1332_, v_resolvedId_1336_, v___x_1337_);
if (v___x_1337_ == 0)
{
goto v___jp_1339_;
}
else
{
uint8_t v___x_1345_; 
lean_inc(v_resolvedId_1336_);
lean_inc_ref(v_env_1332_);
v___x_1345_ = l_Lean_isProtected(v_env_1332_, v_resolvedId_1336_);
if (v___x_1345_ == 0)
{
goto v___jp_1339_;
}
else
{
lean_dec(v_resolvedId_1336_);
lean_dec_ref(v_env_1332_);
return v_resolvedIds_1338_;
}
}
v___jp_1339_:
{
uint8_t v___x_1340_; 
lean_inc(v_resolvedId_1336_);
lean_inc_ref(v_env_1332_);
v___x_1340_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1332_, v_resolvedId_1336_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1332_, v_opts_1333_, v_resolvedId_1336_);
if (lean_obj_tag(v___x_1341_) == 1)
{
lean_object* v_val_1342_; lean_object* v___x_1343_; 
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_val_1342_);
lean_ctor_set(v___x_1343_, 1, v_resolvedIds_1338_);
return v___x_1343_;
}
else
{
lean_dec(v___x_1341_);
return v_resolvedIds_1338_;
}
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v_env_1332_);
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_resolvedId_1336_);
lean_ctor_set(v___x_1344_, 1, v_resolvedIds_1338_);
return v___x_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1346_, lean_object* v_opts_1347_, lean_object* v_ns_1348_, lean_object* v_id_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1346_, v_opts_1347_, v_ns_1348_, v_id_1349_);
lean_dec_ref(v_opts_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1351_, lean_object* v_opts_1352_, lean_object* v_id_1353_, lean_object* v_x_1354_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 1)
{
lean_object* v_pre_1355_; lean_object* v___x_1356_; 
v_pre_1355_ = lean_ctor_get(v_x_1354_, 0);
lean_inc(v_pre_1355_);
lean_inc(v_id_1353_);
lean_inc_ref(v_env_1351_);
v___x_1356_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1351_, v_opts_1352_, v_x_1354_, v_id_1353_);
if (lean_obj_tag(v___x_1356_) == 0)
{
v_x_1354_ = v_pre_1355_;
goto _start;
}
else
{
lean_dec(v_pre_1355_);
lean_dec(v_id_1353_);
lean_dec_ref(v_env_1351_);
return v___x_1356_;
}
}
else
{
lean_object* v___x_1358_; 
lean_dec(v_x_1354_);
lean_dec(v_id_1353_);
lean_dec_ref(v_env_1351_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1359_, lean_object* v_opts_1360_, lean_object* v_id_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1359_, v_opts_1360_, v_id_1361_, v_x_1362_);
lean_dec_ref(v_opts_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1364_, lean_object* v_opts_1365_, lean_object* v_id_1366_){
_start:
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_Name_isAtomic(v_id_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_resolvedId_1370_; uint8_t v___x_1371_; 
v___x_1368_ = l_Lean_rootNamespace;
v___x_1369_ = lean_box(0);
v_resolvedId_1370_ = l_Lean_Name_replacePrefix(v_id_1366_, v___x_1368_, v___x_1369_);
lean_inc(v_resolvedId_1370_);
lean_inc_ref(v_env_1364_);
v___x_1371_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1364_, v_resolvedId_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1364_, v_opts_1365_, v_resolvedId_1370_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; 
lean_dec_ref(v_env_1364_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_resolvedId_1370_);
return v___x_1373_;
}
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_id_1366_);
lean_dec_ref(v_env_1364_);
v___x_1374_ = lean_box(0);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1375_, lean_object* v_opts_1376_, lean_object* v_id_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1375_, v_opts_1376_, v_id_1377_);
lean_dec_ref(v_opts_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1379_, lean_object* v_opts_1380_, lean_object* v_id_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_dec(v_id_1381_);
lean_dec_ref(v_env_1379_);
return v_x_1383_;
}
else
{
lean_object* v_head_1384_; 
v_head_1384_ = lean_ctor_get(v_x_1382_, 0);
lean_inc(v_head_1384_);
if (lean_obj_tag(v_head_1384_) == 0)
{
lean_object* v_tail_1385_; lean_object* v_ns_1386_; lean_object* v_except_1387_; uint8_t v___x_1388_; 
v_tail_1385_ = lean_ctor_get(v_x_1382_, 1);
lean_inc(v_tail_1385_);
lean_dec_ref_known(v_x_1382_, 2);
v_ns_1386_ = lean_ctor_get(v_head_1384_, 0);
lean_inc(v_ns_1386_);
v_except_1387_ = lean_ctor_get(v_head_1384_, 1);
lean_inc(v_except_1387_);
lean_dec_ref_known(v_head_1384_, 2);
v___x_1388_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1381_, v_except_1387_);
lean_dec(v_except_1387_);
if (v___x_1388_ == 0)
{
lean_object* v_newResolvedIds_1389_; lean_object* v___x_1390_; 
lean_inc(v_id_1381_);
lean_inc_ref(v_env_1379_);
v_newResolvedIds_1389_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1379_, v_opts_1380_, v_ns_1386_, v_id_1381_);
v___x_1390_ = l_List_appendTR___redArg(v_newResolvedIds_1389_, v_x_1383_);
v_x_1382_ = v_tail_1385_;
v_x_1383_ = v___x_1390_;
goto _start;
}
else
{
lean_dec(v_ns_1386_);
v_x_1382_ = v_tail_1385_;
goto _start;
}
}
else
{
lean_object* v_tail_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1413_; 
v_tail_1393_ = lean_ctor_get(v_x_1382_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1414_);
v___x_1395_ = v_x_1382_;
v_isShared_1396_ = v_isSharedCheck_1413_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_tail_1393_);
lean_dec(v_x_1382_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1413_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_id_1397_; lean_object* v_declName_1398_; uint8_t v___x_1399_; 
v_id_1397_ = lean_ctor_get(v_head_1384_, 0);
lean_inc(v_id_1397_);
v_declName_1398_ = lean_ctor_get(v_head_1384_, 1);
lean_inc(v_declName_1398_);
lean_dec_ref_known(v_head_1384_, 2);
v___x_1399_ = lean_name_eq(v_id_1397_, v_id_1381_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lean_Name_isPrefixOf(v_id_1397_, v_id_1381_);
if (v___x_1400_ == 0)
{
lean_dec(v_declName_1398_);
lean_dec(v_id_1397_);
lean_del_object(v___x_1395_);
v_x_1382_ = v_tail_1393_;
goto _start;
}
else
{
lean_object* v_candidate_1402_; uint8_t v___x_1403_; 
lean_inc(v_id_1381_);
v_candidate_1402_ = l_Lean_Name_replacePrefix(v_id_1381_, v_id_1397_, v_declName_1398_);
lean_dec(v_declName_1398_);
lean_dec(v_id_1397_);
lean_inc(v_candidate_1402_);
lean_inc_ref(v_env_1379_);
v___x_1403_ = l_Lean_Environment_contains(v_env_1379_, v_candidate_1402_, v___x_1400_);
if (v___x_1403_ == 0)
{
lean_dec(v_candidate_1402_);
lean_del_object(v___x_1395_);
v_x_1382_ = v_tail_1393_;
goto _start;
}
else
{
lean_object* v___x_1406_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v_x_1383_);
lean_ctor_set(v___x_1395_, 0, v_candidate_1402_);
v___x_1406_ = v___x_1395_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_candidate_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_x_1383_);
v___x_1406_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v_x_1382_ = v_tail_1393_;
v_x_1383_ = v___x_1406_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_id_1397_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v_x_1383_);
lean_ctor_set(v___x_1395_, 0, v_declName_1398_);
v___x_1410_ = v___x_1395_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_declName_1398_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_x_1383_);
v___x_1410_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v_x_1382_ = v_tail_1393_;
v_x_1383_ = v___x_1410_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1415_, lean_object* v_opts_1416_, lean_object* v_id_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1415_, v_opts_1416_, v_id_1417_, v_x_1418_, v_x_1419_);
lean_dec_ref(v_opts_1416_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1422_){
_start:
{
lean_object* v___f_1423_; lean_object* v___x_1424_; 
v___f_1423_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1424_ = l_List_eraseDupsBy___redArg(v___f_1423_, v_as_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
if (lean_obj_tag(v_a_1426_) == 0)
{
lean_object* v___x_1428_; 
lean_dec(v_projs_1425_);
v___x_1428_ = l_List_reverse___redArg(v_a_1427_);
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1439_; 
v_head_1429_ = lean_ctor_get(v_a_1426_, 0);
v_tail_1430_ = lean_ctor_get(v_a_1426_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1426_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1432_ = v_a_1426_;
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_tail_1430_);
lean_inc(v_head_1429_);
lean_dec(v_a_1426_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_inc(v_projs_1425_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_head_1429_);
lean_ctor_set(v___x_1434_, 1, v_projs_1425_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v_a_1427_);
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_a_1427_);
v___x_1436_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v_a_1426_ = v_tail_1430_;
v_a_1427_ = v___x_1436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1440_, lean_object* v_opts_1441_, lean_object* v_ns_1442_, lean_object* v_openDecls_1443_, lean_object* v_extractionResult_1444_, lean_object* v_id_1445_, lean_object* v_projs_1446_){
_start:
{
if (lean_obj_tag(v_id_1445_) == 1)
{
lean_object* v_pre_1447_; lean_object* v_str_1448_; lean_object* v_imported_1449_; lean_object* v_ctx_1450_; lean_object* v_scopes_1451_; lean_object* v___x_1452_; lean_object* v_id_1453_; lean_object* v___y_1455_; lean_object* v___x_1465_; lean_object* v___y_1467_; 
v_pre_1447_ = lean_ctor_get(v_id_1445_, 0);
lean_inc(v_pre_1447_);
v_str_1448_ = lean_ctor_get(v_id_1445_, 1);
lean_inc_ref(v_str_1448_);
v_imported_1449_ = lean_ctor_get(v_extractionResult_1444_, 1);
v_ctx_1450_ = lean_ctor_get(v_extractionResult_1444_, 2);
v_scopes_1451_ = lean_ctor_get(v_extractionResult_1444_, 3);
lean_inc(v_scopes_1451_);
lean_inc(v_ctx_1450_);
lean_inc(v_imported_1449_);
v___x_1452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1452_, 0, v_id_1445_);
lean_ctor_set(v___x_1452_, 1, v_imported_1449_);
lean_ctor_set(v___x_1452_, 2, v_ctx_1450_);
lean_ctor_set(v___x_1452_, 3, v_scopes_1451_);
v_id_1453_ = l_Lean_MacroScopesView_review(v___x_1452_);
lean_inc(v_ns_1442_);
lean_inc(v_id_1453_);
lean_inc_ref(v_env_1440_);
v___x_1465_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1440_, v_opts_1441_, v_id_1453_, v_ns_1442_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1472_; 
lean_inc(v_id_1453_);
lean_inc_ref(v_env_1440_);
v___x_1472_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1440_, v_opts_1441_, v_id_1453_);
if (lean_obj_tag(v___x_1472_) == 0)
{
uint8_t v___x_1473_; 
lean_inc(v_id_1453_);
lean_inc_ref(v_env_1440_);
v___x_1473_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1440_, v_id_1453_);
if (v___x_1473_ == 0)
{
v___y_1467_ = v___x_1465_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1474_; 
lean_inc(v_id_1453_);
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_id_1453_);
lean_ctor_set(v___x_1474_, 1, v___x_1465_);
v___y_1467_ = v___x_1474_;
goto v___jp_1466_;
}
}
else
{
lean_object* v_val_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v_id_1453_);
lean_dec_ref(v_str_1448_);
lean_dec(v_pre_1447_);
lean_dec(v_openDecls_1443_);
lean_dec(v_ns_1442_);
lean_dec_ref(v_env_1440_);
v_val_1475_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_val_1475_);
lean_ctor_set(v___x_1476_, 1, v_projs_1446_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
return v___x_1478_;
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_id_1453_);
lean_dec_ref(v_str_1448_);
lean_dec(v_pre_1447_);
lean_dec(v_openDecls_1443_);
lean_dec(v_ns_1442_);
lean_dec_ref(v_env_1440_);
v___x_1479_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1465_);
v___x_1480_ = lean_box(0);
v___x_1481_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1446_, v___x_1479_, v___x_1480_);
return v___x_1481_;
}
v___jp_1454_:
{
lean_object* v_resolvedIds_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v_resolvedIds_1459_; 
lean_inc(v_openDecls_1443_);
lean_inc(v_id_1453_);
lean_inc_ref_n(v_env_1440_, 2);
v_resolvedIds_1456_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1440_, v_opts_1441_, v_id_1453_, v_openDecls_1443_, v___y_1455_);
v___x_1457_ = l_Lean_Name_isAtomic(v_id_1453_);
v___x_1458_ = l_Lean_getAliases(v_env_1440_, v_id_1453_, v___x_1457_);
lean_dec(v_id_1453_);
v_resolvedIds_1459_ = l_List_appendTR___redArg(v___x_1458_, v_resolvedIds_1456_);
if (lean_obj_tag(v_resolvedIds_1459_) == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_str_1448_);
lean_ctor_set(v___x_1460_, 1, v_projs_1446_);
v_id_1445_ = v_pre_1447_;
v_projs_1446_ = v___x_1460_;
goto _start;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec_ref(v_str_1448_);
lean_dec(v_pre_1447_);
lean_dec(v_openDecls_1443_);
lean_dec(v_ns_1442_);
lean_dec_ref(v_env_1440_);
v___x_1462_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1459_);
v___x_1463_ = lean_box(0);
v___x_1464_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1446_, v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
v___jp_1466_:
{
lean_object* v___x_1468_; 
lean_inc(v_id_1453_);
lean_inc_ref(v_env_1440_);
v___x_1468_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1440_, v_opts_1441_, v_id_1453_);
if (lean_obj_tag(v___x_1468_) == 1)
{
lean_object* v_val_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_val_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_val_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_val_1469_);
lean_ctor_set(v___x_1470_, 1, v___x_1465_);
v___x_1471_ = l_List_appendTR___redArg(v___x_1470_, v___y_1467_);
v___y_1455_ = v___x_1471_;
goto v___jp_1454_;
}
else
{
lean_dec(v___x_1468_);
lean_dec(v___x_1465_);
v___y_1455_ = v___y_1467_;
goto v___jp_1454_;
}
}
}
else
{
lean_object* v___x_1482_; 
lean_dec(v_projs_1446_);
lean_dec(v_id_1445_);
lean_dec(v_openDecls_1443_);
lean_dec(v_ns_1442_);
lean_dec_ref(v_env_1440_);
v___x_1482_ = lean_box(0);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1483_, lean_object* v_opts_1484_, lean_object* v_ns_1485_, lean_object* v_openDecls_1486_, lean_object* v_extractionResult_1487_, lean_object* v_id_1488_, lean_object* v_projs_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1483_, v_opts_1484_, v_ns_1485_, v_openDecls_1486_, v_extractionResult_1487_, v_id_1488_, v_projs_1489_);
lean_dec_ref(v_extractionResult_1487_);
lean_dec_ref(v_opts_1484_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1491_, lean_object* v_opts_1492_, lean_object* v_ns_1493_, lean_object* v_openDecls_1494_, lean_object* v_id_1495_){
_start:
{
lean_object* v_extractionResult_1496_; lean_object* v_name_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_extractionResult_1496_ = l_Lean_extractMacroScopes(v_id_1495_);
v_name_1497_ = lean_ctor_get(v_extractionResult_1496_, 0);
lean_inc(v_name_1497_);
v___x_1498_ = lean_box(0);
v___x_1499_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1491_, v_opts_1492_, v_ns_1493_, v_openDecls_1494_, v_extractionResult_1496_, v_name_1497_, v___x_1498_);
lean_dec_ref(v_extractionResult_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1500_, lean_object* v_opts_1501_, lean_object* v_ns_1502_, lean_object* v_openDecls_1503_, lean_object* v_id_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_ResolveName_resolveGlobalName(v_env_1500_, v_opts_1501_, v_ns_1502_, v_openDecls_1503_, v_id_1504_);
lean_dec_ref(v_opts_1501_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_panic_fn_borrowed(v___x_1507_, v_msg_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1512_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1513_ = lean_unsigned_to_nat(9u);
v___x_1514_ = lean_unsigned_to_nat(230u);
v___x_1515_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1516_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1517_ = l_mkPanicMessageWithDecl(v___x_1516_, v___x_1515_, v___x_1514_, v___x_1513_, v___x_1512_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1518_, lean_object* v_n_1519_, lean_object* v_ns_1520_){
_start:
{
switch(lean_obj_tag(v_ns_1520_))
{
case 1:
{
lean_object* v_pre_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_pre_1521_ = lean_ctor_get(v_ns_1520_, 0);
lean_inc(v_pre_1521_);
lean_inc(v_n_1519_);
v___x_1522_ = l_Lean_Name_append(v_ns_1520_, v_n_1519_);
lean_inc_ref(v_env_1518_);
v___x_1523_ = l_Lean_Environment_isNamespace(v_env_1518_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec(v___x_1522_);
v_ns_1520_ = v_pre_1521_;
goto _start;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_pre_1521_);
lean_dec(v_n_1519_);
lean_dec_ref(v_env_1518_);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1522_);
return v___x_1525_;
}
}
case 0:
{
lean_object* v___x_1526_; lean_object* v_n_1527_; uint8_t v___x_1528_; 
v___x_1526_ = l_Lean_rootNamespace;
v_n_1527_ = l_Lean_Name_replacePrefix(v_n_1519_, v___x_1526_, v_ns_1520_);
v___x_1528_ = l_Lean_Environment_isNamespace(v_env_1518_, v_n_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v_n_1527_);
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_n_1527_);
return v___x_1530_;
}
}
default: 
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_ns_1520_);
lean_dec(v_n_1519_);
lean_dec_ref(v_env_1518_);
v___x_1531_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1532_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1531_);
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1533_, lean_object* v_n_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_object* v___x_1536_; 
lean_dec(v_n_1534_);
lean_dec_ref(v_env_1533_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
else
{
lean_object* v_head_1537_; 
v_head_1537_ = lean_ctor_get(v_x_1535_, 0);
if (lean_obj_tag(v_head_1537_) == 0)
{
lean_object* v_tail_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1555_; 
lean_inc_ref(v_head_1537_);
v_tail_1538_ = lean_ctor_get(v_x_1535_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_x_1535_, 0);
lean_dec(v_unused_1556_);
v___x_1540_ = v_x_1535_;
v_isShared_1541_ = v_isSharedCheck_1555_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_tail_1538_);
lean_dec(v_x_1535_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1555_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_ns_1542_; lean_object* v_except_1543_; lean_object* v___x_1544_; uint8_t v___y_1546_; uint8_t v___x_1552_; 
v_ns_1542_ = lean_ctor_get(v_head_1537_, 0);
lean_inc(v_ns_1542_);
v_except_1543_ = lean_ctor_get(v_head_1537_, 1);
lean_inc(v_except_1543_);
lean_dec_ref_known(v_head_1537_, 2);
lean_inc(v_n_1534_);
v___x_1544_ = l_Lean_Name_append(v_ns_1542_, v_n_1534_);
lean_inc_ref(v_env_1533_);
v___x_1552_ = l_Lean_Environment_isNamespace(v_env_1533_, v___x_1544_);
if (v___x_1552_ == 0)
{
lean_dec(v_except_1543_);
v___y_1546_ = v___x_1552_;
goto v___jp_1545_;
}
else
{
uint8_t v___x_1553_; 
v___x_1553_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1534_, v_except_1543_);
lean_dec(v_except_1543_);
if (v___x_1553_ == 0)
{
v___y_1546_ = v___x_1552_;
goto v___jp_1545_;
}
else
{
lean_dec(v___x_1544_);
lean_del_object(v___x_1540_);
v_x_1535_ = v_tail_1538_;
goto _start;
}
}
v___jp_1545_:
{
if (v___y_1546_ == 0)
{
lean_dec(v___x_1544_);
lean_del_object(v___x_1540_);
v_x_1535_ = v_tail_1538_;
goto _start;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1533_, v_n_1534_, v_tail_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___x_1548_);
lean_ctor_set(v___x_1540_, 0, v___x_1544_);
v___x_1550_ = v___x_1540_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_object* v_tail_1557_; 
v_tail_1557_ = lean_ctor_get(v_x_1535_, 1);
lean_inc(v_tail_1557_);
lean_dec_ref_known(v_x_1535_, 2);
v_x_1535_ = v_tail_1557_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1559_, lean_object* v_ns_1560_, lean_object* v_openDecls_1561_, lean_object* v_id_1562_){
_start:
{
lean_object* v___x_1563_; 
lean_inc(v_id_1562_);
lean_inc_ref(v_env_1559_);
v___x_1563_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1559_, v_id_1562_, v_ns_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1559_, v_id_1562_, v_openDecls_1561_);
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_val_1565_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1566_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1559_, v_id_1562_, v_openDecls_1561_);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_val_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1568_, lean_object* v_inst_1569_){
_start:
{
lean_object* v_getCurrNamespace_1570_; lean_object* v_getOpenDecls_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1580_; 
v_getCurrNamespace_1570_ = lean_ctor_get(v_inst_1569_, 0);
v_getOpenDecls_1571_ = lean_ctor_get(v_inst_1569_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_inst_1569_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1573_ = v_inst_1569_;
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_getOpenDecls_1571_);
lean_inc(v_getCurrNamespace_1570_);
lean_dec(v_inst_1569_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_inc(v_inst_1568_);
v___x_1575_ = lean_apply_2(v_inst_1568_, lean_box(0), v_getCurrNamespace_1570_);
v___x_1576_ = lean_apply_2(v_inst_1568_, lean_box(0), v_getOpenDecls_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1576_);
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1581_, lean_object* v_n_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1583_, v_inst_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1588_ = l_Lean_stringToMessageData(v___x_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1592_, lean_object* v_toPure_1593_, lean_object* v_id_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, uint8_t v_____do__lift_1599_){
_start:
{
uint8_t v_isExporting_1603_; 
v_isExporting_1603_ = lean_ctor_get_uint8(v_____do__lift_1592_, sizeof(void*)*8);
if (v_isExporting_1603_ == 0)
{
lean_dec(v_inst_1598_);
lean_dec(v_inst_1597_);
lean_dec_ref(v_inst_1596_);
lean_dec_ref(v_inst_1595_);
lean_dec(v_id_1594_);
goto v___jp_1600_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_isPrivateName(v_id_1594_);
if (v___x_1604_ == 0)
{
lean_dec(v_inst_1598_);
lean_dec(v_inst_1597_);
lean_dec_ref(v_inst_1596_);
lean_dec_ref(v_inst_1595_);
lean_dec(v_id_1594_);
goto v___jp_1600_;
}
else
{
if (v_____do__lift_1599_ == 0)
{
lean_dec(v_inst_1598_);
lean_dec(v_inst_1597_);
lean_dec_ref(v_inst_1596_);
lean_dec_ref(v_inst_1595_);
lean_dec(v_id_1594_);
goto v___jp_1600_;
}
else
{
lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v_toPure_1593_);
v___x_1605_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1606_ = 0;
v___x_1607_ = l_Lean_MessageData_ofConstName(v_id_1594_, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1605_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_logWarning___redArg(v_inst_1595_, v_inst_1596_, v_inst_1597_, v_inst_1598_, v___x_1610_);
return v___x_1611_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_apply_2(v_toPure_1593_, lean_box(0), v___x_1601_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1612_, lean_object* v_toPure_1613_, lean_object* v_id_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_____do__lift_1619_){
_start:
{
uint8_t v_____do__lift_199__boxed_1620_; lean_object* v_res_1621_; 
v_____do__lift_199__boxed_1620_ = lean_unbox(v_____do__lift_1619_);
v_res_1621_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1612_, v_toPure_1613_, v_id_1614_, v_inst_1615_, v_inst_1616_, v_inst_1617_, v_inst_1618_, v_____do__lift_199__boxed_1620_);
lean_dec_ref(v_____do__lift_1612_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1622_, lean_object* v_id_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v___x_1628_, lean_object* v_toBind_1629_, lean_object* v_____do__lift_1630_){
_start:
{
lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_inc(v_inst_1627_);
lean_inc_ref(v_inst_1624_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1631_, 0, v_____do__lift_1630_);
lean_closure_set(v___f_1631_, 1, v_toPure_1622_);
lean_closure_set(v___f_1631_, 2, v_id_1623_);
lean_closure_set(v___f_1631_, 3, v_inst_1624_);
lean_closure_set(v___f_1631_, 4, v_inst_1625_);
lean_closure_set(v___f_1631_, 5, v_inst_1626_);
lean_closure_set(v___f_1631_, 6, v_inst_1627_);
v___x_1632_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1633_ = l_Lean_Option_getM___redArg(v_inst_1624_, v_inst_1627_, v___x_1628_, v___x_1632_);
v___x_1634_ = lean_apply_4(v_toBind_1629_, lean_box(0), lean_box(0), v___x_1633_, v___f_1631_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_id_1640_){
_start:
{
lean_object* v___x_1641_; lean_object* v_toApplicative_1642_; lean_object* v_toBind_1643_; lean_object* v_getEnv_1644_; lean_object* v_toPure_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; 
v___x_1641_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1642_ = lean_ctor_get(v_inst_1635_, 0);
v_toBind_1643_ = lean_ctor_get(v_inst_1635_, 1);
lean_inc_n(v_toBind_1643_, 2);
v_getEnv_1644_ = lean_ctor_get(v_inst_1636_, 0);
lean_inc(v_getEnv_1644_);
lean_dec_ref(v_inst_1636_);
v_toPure_1645_ = lean_ctor_get(v_toApplicative_1642_, 1);
lean_inc(v_toPure_1645_);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1646_, 0, v_toPure_1645_);
lean_closure_set(v___f_1646_, 1, v_id_1640_);
lean_closure_set(v___f_1646_, 2, v_inst_1635_);
lean_closure_set(v___f_1646_, 3, v_inst_1638_);
lean_closure_set(v___f_1646_, 4, v_inst_1639_);
lean_closure_set(v___f_1646_, 5, v_inst_1637_);
lean_closure_set(v___f_1646_, 6, v___x_1641_);
lean_closure_set(v___f_1646_, 7, v_toBind_1643_);
v___x_1647_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v_getEnv_1644_, v___f_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_id_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1649_, v_inst_1650_, v_inst_1651_, v_inst_1652_, v_inst_1653_, v_id_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1656_, lean_object* v_n_1657_, lean_object* v_toPure_1658_, uint8_t v___y_1659_, uint8_t v___x_1660_, lean_object* v_____r_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1656_, v_n_1657_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_box(v___y_1659_);
v___x_1664_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1663_);
return v___x_1664_;
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1666_; uint8_t v_isModule_1667_; 
v_val_1665_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v___x_1662_, 1);
v___x_1666_ = l_Lean_Environment_header(v_env_1656_);
v_isModule_1667_ = lean_ctor_get_uint8(v___x_1666_, sizeof(void*)*7 + 4);
if (v_isModule_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___x_1666_);
lean_dec(v_val_1665_);
v___x_1668_ = lean_box(v___x_1660_);
v___x_1669_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1668_);
return v___x_1669_;
}
else
{
lean_object* v_modules_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_modules_1670_ = lean_ctor_get(v___x_1666_, 3);
lean_inc_ref(v_modules_1670_);
lean_dec_ref(v___x_1666_);
v___x_1671_ = lean_array_get_size(v_modules_1670_);
v___x_1672_ = lean_nat_dec_lt(v_val_1665_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v_modules_1670_);
lean_dec(v_val_1665_);
v___x_1673_ = lean_box(v_isModule_1667_);
v___x_1674_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1673_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; lean_object* v_toImport_1676_; uint8_t v_importAll_1677_; 
v___x_1675_ = lean_array_fget(v_modules_1670_, v_val_1665_);
lean_dec(v_val_1665_);
lean_dec_ref(v_modules_1670_);
v_toImport_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_ref(v_toImport_1676_);
lean_dec(v___x_1675_);
v_importAll_1677_ = lean_ctor_get_uint8(v_toImport_1676_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1676_);
if (v_importAll_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_box(v_isModule_1667_);
v___x_1679_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1678_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_box(v___y_1659_);
v___x_1681_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1680_);
return v___x_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1682_, lean_object* v_n_1683_, lean_object* v_toPure_1684_, lean_object* v___y_1685_, lean_object* v___x_1686_, lean_object* v_____r_1687_){
_start:
{
uint8_t v___y_386__boxed_1688_; uint8_t v___x_387__boxed_1689_; lean_object* v_res_1690_; 
v___y_386__boxed_1688_ = lean_unbox(v___y_1685_);
v___x_387__boxed_1689_ = lean_unbox(v___x_1686_);
v_res_1690_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1682_, v_n_1683_, v_toPure_1684_, v___y_386__boxed_1688_, v___x_387__boxed_1689_, v_____r_1687_);
lean_dec(v_n_1683_);
lean_dec_ref(v_env_1682_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1691_, lean_object* v_n_1692_, lean_object* v_toPure_1693_, uint8_t v___x_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_toBind_1700_, uint8_t v___y_1701_, uint8_t v_____do__lift_1702_){
_start:
{
uint8_t v___y_1704_; uint8_t v_isExporting_1710_; 
v_isExporting_1710_ = lean_ctor_get_uint8(v_env_1691_, sizeof(void*)*8);
if (v_isExporting_1710_ == 0)
{
v___y_1704_ = v___y_1701_;
goto v___jp_1703_;
}
else
{
if (v_____do__lift_1702_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v_toBind_1700_);
lean_dec(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec(v_inst_1697_);
lean_dec_ref(v_inst_1696_);
lean_dec_ref(v_inst_1695_);
lean_dec(v_n_1692_);
lean_dec_ref(v_env_1691_);
v___x_1711_ = lean_box(v___x_1694_);
v___x_1712_ = lean_apply_2(v_toPure_1693_, lean_box(0), v___x_1711_);
return v___x_1712_;
}
else
{
v___y_1704_ = v___y_1701_;
goto v___jp_1703_;
}
}
v___jp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1705_ = lean_box(v___y_1704_);
v___x_1706_ = lean_box(v___x_1694_);
lean_inc(v_n_1692_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1707_, 0, v_env_1691_);
lean_closure_set(v___f_1707_, 1, v_n_1692_);
lean_closure_set(v___f_1707_, 2, v_toPure_1693_);
lean_closure_set(v___f_1707_, 3, v___x_1705_);
lean_closure_set(v___f_1707_, 4, v___x_1706_);
v___x_1708_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1695_, v_inst_1696_, v_inst_1697_, v_inst_1698_, v_inst_1699_, v_n_1692_);
v___x_1709_ = lean_apply_4(v_toBind_1700_, lean_box(0), lean_box(0), v___x_1708_, v___f_1707_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1713_, lean_object* v_n_1714_, lean_object* v_toPure_1715_, lean_object* v___x_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_toBind_1722_, lean_object* v___y_1723_, lean_object* v_____do__lift_1724_){
_start:
{
uint8_t v___x_427__boxed_1725_; uint8_t v___y_433__boxed_1726_; uint8_t v_____do__lift_434__boxed_1727_; lean_object* v_res_1728_; 
v___x_427__boxed_1725_ = lean_unbox(v___x_1716_);
v___y_433__boxed_1726_ = lean_unbox(v___y_1723_);
v_____do__lift_434__boxed_1727_ = lean_unbox(v_____do__lift_1724_);
v_res_1728_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1713_, v_n_1714_, v_toPure_1715_, v___x_427__boxed_1725_, v_inst_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_toBind_1722_, v___y_433__boxed_1726_, v_____do__lift_434__boxed_1727_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1729_, lean_object* v_toPure_1730_, uint8_t v___x_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_toBind_1737_, uint8_t v___y_1738_, lean_object* v___x_1739_, lean_object* v_env_1740_){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1741_ = lean_box(v___x_1731_);
v___x_1742_ = lean_box(v___y_1738_);
lean_inc(v_toBind_1737_);
lean_inc(v_inst_1734_);
lean_inc_ref(v_inst_1732_);
v___f_1743_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1743_, 0, v_env_1740_);
lean_closure_set(v___f_1743_, 1, v_n_1729_);
lean_closure_set(v___f_1743_, 2, v_toPure_1730_);
lean_closure_set(v___f_1743_, 3, v___x_1741_);
lean_closure_set(v___f_1743_, 4, v_inst_1732_);
lean_closure_set(v___f_1743_, 5, v_inst_1733_);
lean_closure_set(v___f_1743_, 6, v_inst_1734_);
lean_closure_set(v___f_1743_, 7, v_inst_1735_);
lean_closure_set(v___f_1743_, 8, v_inst_1736_);
lean_closure_set(v___f_1743_, 9, v_toBind_1737_);
lean_closure_set(v___f_1743_, 10, v___x_1742_);
v___x_1744_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1745_ = l_Lean_Option_getM___redArg(v_inst_1732_, v_inst_1734_, v___x_1739_, v___x_1744_);
v___x_1746_ = lean_apply_4(v_toBind_1737_, lean_box(0), lean_box(0), v___x_1745_, v___f_1743_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1747_, lean_object* v_toPure_1748_, lean_object* v___x_1749_, lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_toBind_1755_, lean_object* v___y_1756_, lean_object* v___x_1757_, lean_object* v_env_1758_){
_start:
{
uint8_t v___x_469__boxed_1759_; uint8_t v___y_475__boxed_1760_; lean_object* v_res_1761_; 
v___x_469__boxed_1759_ = lean_unbox(v___x_1749_);
v___y_475__boxed_1760_ = lean_unbox(v___y_1756_);
v_res_1761_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1747_, v_toPure_1748_, v___x_469__boxed_1759_, v_inst_1750_, v_inst_1751_, v_inst_1752_, v_inst_1753_, v_inst_1754_, v_toBind_1755_, v___y_475__boxed_1760_, v___x_1757_, v_env_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_n_1767_){
_start:
{
lean_object* v___x_1768_; uint8_t v___y_1770_; uint8_t v___x_1785_; 
v___x_1768_ = l_Lean_KVMap_instValueBool;
v___x_1785_ = l_Lean_isPrivateName(v_n_1767_);
if (v___x_1785_ == 0)
{
uint8_t v___x_1786_; 
v___x_1786_ = 1;
v___y_1770_ = v___x_1786_;
goto v___jp_1769_;
}
else
{
uint8_t v___x_1787_; 
v___x_1787_ = 0;
v___y_1770_ = v___x_1787_;
goto v___jp_1769_;
}
v___jp_1769_:
{
if (v___y_1770_ == 0)
{
lean_object* v_toApplicative_1771_; lean_object* v_toBind_1772_; lean_object* v_toPure_1773_; lean_object* v_getEnv_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; lean_object* v___x_1779_; 
v_toApplicative_1771_ = lean_ctor_get(v_inst_1764_, 0);
v_toBind_1772_ = lean_ctor_get(v_inst_1764_, 1);
lean_inc_n(v_toBind_1772_, 2);
v_toPure_1773_ = lean_ctor_get(v_toApplicative_1771_, 1);
lean_inc(v_toPure_1773_);
v_getEnv_1774_ = lean_ctor_get(v_inst_1765_, 0);
lean_inc(v_getEnv_1774_);
v___x_1775_ = 1;
v___x_1776_ = lean_box(v___x_1775_);
v___x_1777_ = lean_box(v___y_1770_);
v___f_1778_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1778_, 0, v_n_1767_);
lean_closure_set(v___f_1778_, 1, v_toPure_1773_);
lean_closure_set(v___f_1778_, 2, v___x_1776_);
lean_closure_set(v___f_1778_, 3, v_inst_1764_);
lean_closure_set(v___f_1778_, 4, v_inst_1765_);
lean_closure_set(v___f_1778_, 5, v_inst_1766_);
lean_closure_set(v___f_1778_, 6, v_inst_1762_);
lean_closure_set(v___f_1778_, 7, v_inst_1763_);
lean_closure_set(v___f_1778_, 8, v_toBind_1772_);
lean_closure_set(v___f_1778_, 9, v___x_1777_);
lean_closure_set(v___f_1778_, 10, v___x_1768_);
v___x_1779_ = lean_apply_4(v_toBind_1772_, lean_box(0), lean_box(0), v_getEnv_1774_, v___f_1778_);
return v___x_1779_;
}
else
{
lean_object* v_toApplicative_1780_; lean_object* v_toPure_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_toApplicative_1780_ = lean_ctor_get(v_inst_1764_, 0);
lean_inc_ref(v_toApplicative_1780_);
lean_dec(v_n_1767_);
lean_dec(v_inst_1766_);
lean_dec_ref(v_inst_1765_);
lean_dec_ref(v_inst_1764_);
lean_dec(v_inst_1763_);
lean_dec_ref(v_inst_1762_);
v_toPure_1781_ = lean_ctor_get(v_toApplicative_1780_, 1);
lean_inc(v_toPure_1781_);
lean_dec_ref(v_toApplicative_1780_);
v___x_1782_ = 0;
v___x_1783_ = lean_box(v___x_1782_);
v___x_1784_ = lean_apply_2(v_toPure_1781_, lean_box(0), v___x_1783_);
return v___x_1784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_n_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1789_, v_inst_1790_, v_inst_1791_, v_inst_1792_, v_inst_1793_, v_n_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1796_){
_start:
{
lean_object* v_fst_1797_; uint8_t v___x_1798_; 
v_fst_1797_ = lean_ctor_get(v_x_1796_, 0);
v___x_1798_ = l_Lean_isPrivateName(v_fst_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1799_){
_start:
{
uint8_t v_res_1800_; lean_object* v_r_1801_; 
v_res_1800_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1799_);
lean_dec_ref(v_x_1799_);
v_r_1801_ = lean_box(v_res_1800_);
return v_r_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1802_, lean_object* v_res_1803_, lean_object* v_____r_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_apply_2(v_toPure_1802_, lean_box(0), v_res_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1806_, lean_object* v_toPure_1807_, lean_object* v_res_1808_, lean_object* v___f_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_toBind_1815_, lean_object* v___f_1816_, lean_object* v_____do__lift_1817_){
_start:
{
if (v_enableLog_1806_ == 0)
{
lean_object* v___x_1818_; 
lean_dec(v___f_1816_);
lean_dec(v_toBind_1815_);
lean_dec(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec(v_inst_1812_);
lean_dec_ref(v_inst_1811_);
lean_dec_ref(v_inst_1810_);
lean_dec_ref(v___f_1809_);
v___x_1818_ = lean_apply_2(v_toPure_1807_, lean_box(0), v_res_1808_);
return v___x_1818_;
}
else
{
uint8_t v_isExporting_1819_; 
v_isExporting_1819_ = lean_ctor_get_uint8(v_____do__lift_1817_, sizeof(void*)*8);
if (v_isExporting_1819_ == 0)
{
lean_object* v___x_1820_; 
lean_dec(v___f_1816_);
lean_dec(v_toBind_1815_);
lean_dec(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec(v_inst_1812_);
lean_dec_ref(v_inst_1811_);
lean_dec_ref(v_inst_1810_);
lean_dec_ref(v___f_1809_);
v___x_1820_ = lean_apply_2(v_toPure_1807_, lean_box(0), v_res_1808_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; 
lean_inc(v_res_1808_);
v___x_1821_ = l_List_find_x3f___redArg(v___f_1809_, v_res_1808_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_object* v_val_1822_; lean_object* v_fst_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v_res_1808_);
lean_dec(v_toPure_1807_);
v_val_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_val_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v_fst_1823_ = lean_ctor_get(v_val_1822_, 0);
lean_inc(v_fst_1823_);
lean_dec(v_val_1822_);
v___x_1824_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1810_, v_inst_1811_, v_inst_1812_, v_inst_1813_, v_inst_1814_, v_fst_1823_);
v___x_1825_ = lean_apply_4(v_toBind_1815_, lean_box(0), lean_box(0), v___x_1824_, v___f_1816_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; 
lean_dec(v___x_1821_);
lean_dec(v___f_1816_);
lean_dec(v_toBind_1815_);
lean_dec(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec(v_inst_1812_);
lean_dec_ref(v_inst_1811_);
lean_dec_ref(v_inst_1810_);
v___x_1826_ = lean_apply_2(v_toPure_1807_, lean_box(0), v_res_1808_);
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1827_, lean_object* v_toPure_1828_, lean_object* v_res_1829_, lean_object* v___f_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_toBind_1836_, lean_object* v___f_1837_, lean_object* v_____do__lift_1838_){
_start:
{
uint8_t v_enableLog_boxed_1839_; lean_object* v_res_1840_; 
v_enableLog_boxed_1839_ = lean_unbox(v_enableLog_1827_);
v_res_1840_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1839_, v_toPure_1828_, v_res_1829_, v___f_1830_, v_inst_1831_, v_inst_1832_, v_inst_1833_, v_inst_1834_, v_inst_1835_, v_toBind_1836_, v___f_1837_, v_____do__lift_1838_);
lean_dec_ref(v_____do__lift_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1841_, lean_object* v_____do__lift_1842_, lean_object* v_____do__lift_1843_, lean_object* v_id_1844_, lean_object* v_toPure_1845_, uint8_t v_enableLog_1846_, lean_object* v___f_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_toBind_1853_, lean_object* v_getEnv_1854_, lean_object* v_____do__lift_1855_){
_start:
{
lean_object* v_res_1856_; lean_object* v___f_1857_; lean_object* v___x_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; 
v_res_1856_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1841_, v_____do__lift_1842_, v_____do__lift_1843_, v_____do__lift_1855_, v_id_1844_);
lean_inc(v_res_1856_);
lean_inc(v_toPure_1845_);
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1857_, 0, v_toPure_1845_);
lean_closure_set(v___f_1857_, 1, v_res_1856_);
v___x_1858_ = lean_box(v_enableLog_1846_);
lean_inc(v_toBind_1853_);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1859_, 0, v___x_1858_);
lean_closure_set(v___f_1859_, 1, v_toPure_1845_);
lean_closure_set(v___f_1859_, 2, v_res_1856_);
lean_closure_set(v___f_1859_, 3, v___f_1847_);
lean_closure_set(v___f_1859_, 4, v_inst_1848_);
lean_closure_set(v___f_1859_, 5, v_inst_1849_);
lean_closure_set(v___f_1859_, 6, v_inst_1850_);
lean_closure_set(v___f_1859_, 7, v_inst_1851_);
lean_closure_set(v___f_1859_, 8, v_inst_1852_);
lean_closure_set(v___f_1859_, 9, v_toBind_1853_);
lean_closure_set(v___f_1859_, 10, v___f_1857_);
v___x_1860_ = lean_apply_4(v_toBind_1853_, lean_box(0), lean_box(0), v_getEnv_1854_, v___f_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1861_, lean_object* v_____do__lift_1862_, lean_object* v_____do__lift_1863_, lean_object* v_id_1864_, lean_object* v_toPure_1865_, lean_object* v_enableLog_1866_, lean_object* v___f_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_toBind_1873_, lean_object* v_getEnv_1874_, lean_object* v_____do__lift_1875_){
_start:
{
uint8_t v_enableLog_boxed_1876_; lean_object* v_res_1877_; 
v_enableLog_boxed_1876_ = lean_unbox(v_enableLog_1866_);
v_res_1877_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1861_, v_____do__lift_1862_, v_____do__lift_1863_, v_id_1864_, v_toPure_1865_, v_enableLog_boxed_1876_, v___f_1867_, v_inst_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_toBind_1873_, v_getEnv_1874_, v_____do__lift_1875_);
lean_dec_ref(v_____do__lift_1862_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1878_, lean_object* v_____do__lift_1879_, lean_object* v_id_1880_, lean_object* v_toPure_1881_, uint8_t v_enableLog_1882_, lean_object* v___f_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_toBind_1889_, lean_object* v_getEnv_1890_, lean_object* v_getOpenDecls_1891_, lean_object* v_____do__lift_1892_){
_start:
{
lean_object* v___x_1893_; lean_object* v___f_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_box(v_enableLog_1882_);
lean_inc(v_toBind_1889_);
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1894_, 0, v_____do__lift_1878_);
lean_closure_set(v___f_1894_, 1, v_____do__lift_1879_);
lean_closure_set(v___f_1894_, 2, v_____do__lift_1892_);
lean_closure_set(v___f_1894_, 3, v_id_1880_);
lean_closure_set(v___f_1894_, 4, v_toPure_1881_);
lean_closure_set(v___f_1894_, 5, v___x_1893_);
lean_closure_set(v___f_1894_, 6, v___f_1883_);
lean_closure_set(v___f_1894_, 7, v_inst_1884_);
lean_closure_set(v___f_1894_, 8, v_inst_1885_);
lean_closure_set(v___f_1894_, 9, v_inst_1886_);
lean_closure_set(v___f_1894_, 10, v_inst_1887_);
lean_closure_set(v___f_1894_, 11, v_inst_1888_);
lean_closure_set(v___f_1894_, 12, v_toBind_1889_);
lean_closure_set(v___f_1894_, 13, v_getEnv_1890_);
v___x_1895_ = lean_apply_4(v_toBind_1889_, lean_box(0), lean_box(0), v_getOpenDecls_1891_, v___f_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1896_, lean_object* v_____do__lift_1897_, lean_object* v_id_1898_, lean_object* v_toPure_1899_, lean_object* v_enableLog_1900_, lean_object* v___f_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_toBind_1907_, lean_object* v_getEnv_1908_, lean_object* v_getOpenDecls_1909_, lean_object* v_____do__lift_1910_){
_start:
{
uint8_t v_enableLog_boxed_1911_; lean_object* v_res_1912_; 
v_enableLog_boxed_1911_ = lean_unbox(v_enableLog_1900_);
v_res_1912_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1896_, v_____do__lift_1897_, v_id_1898_, v_toPure_1899_, v_enableLog_boxed_1911_, v___f_1901_, v_inst_1902_, v_inst_1903_, v_inst_1904_, v_inst_1905_, v_inst_1906_, v_toBind_1907_, v_getEnv_1908_, v_getOpenDecls_1909_, v_____do__lift_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1913_, lean_object* v_____do__lift_1914_, lean_object* v_id_1915_, lean_object* v_toPure_1916_, uint8_t v_enableLog_1917_, lean_object* v___f_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_toBind_1924_, lean_object* v_getEnv_1925_, lean_object* v_____do__lift_1926_){
_start:
{
lean_object* v_getCurrNamespace_1927_; lean_object* v_getOpenDecls_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
v_getCurrNamespace_1927_ = lean_ctor_get(v_inst_1913_, 0);
lean_inc(v_getCurrNamespace_1927_);
v_getOpenDecls_1928_ = lean_ctor_get(v_inst_1913_, 1);
lean_inc(v_getOpenDecls_1928_);
lean_dec_ref(v_inst_1913_);
v___x_1929_ = lean_box(v_enableLog_1917_);
lean_inc(v_toBind_1924_);
v___f_1930_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1930_, 0, v_____do__lift_1914_);
lean_closure_set(v___f_1930_, 1, v_____do__lift_1926_);
lean_closure_set(v___f_1930_, 2, v_id_1915_);
lean_closure_set(v___f_1930_, 3, v_toPure_1916_);
lean_closure_set(v___f_1930_, 4, v___x_1929_);
lean_closure_set(v___f_1930_, 5, v___f_1918_);
lean_closure_set(v___f_1930_, 6, v_inst_1919_);
lean_closure_set(v___f_1930_, 7, v_inst_1920_);
lean_closure_set(v___f_1930_, 8, v_inst_1921_);
lean_closure_set(v___f_1930_, 9, v_inst_1922_);
lean_closure_set(v___f_1930_, 10, v_inst_1923_);
lean_closure_set(v___f_1930_, 11, v_toBind_1924_);
lean_closure_set(v___f_1930_, 12, v_getEnv_1925_);
lean_closure_set(v___f_1930_, 13, v_getOpenDecls_1928_);
v___x_1931_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v_getCurrNamespace_1927_, v___f_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1932_, lean_object* v_____do__lift_1933_, lean_object* v_id_1934_, lean_object* v_toPure_1935_, lean_object* v_enableLog_1936_, lean_object* v___f_1937_, lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_toBind_1943_, lean_object* v_getEnv_1944_, lean_object* v_____do__lift_1945_){
_start:
{
uint8_t v_enableLog_boxed_1946_; lean_object* v_res_1947_; 
v_enableLog_boxed_1946_ = lean_unbox(v_enableLog_1936_);
v_res_1947_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1932_, v_____do__lift_1933_, v_id_1934_, v_toPure_1935_, v_enableLog_boxed_1946_, v___f_1937_, v_inst_1938_, v_inst_1939_, v_inst_1940_, v_inst_1941_, v_inst_1942_, v_toBind_1943_, v_getEnv_1944_, v_____do__lift_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1948_, lean_object* v_id_1949_, lean_object* v_toPure_1950_, uint8_t v_enableLog_1951_, lean_object* v___f_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_toBind_1958_, lean_object* v_getEnv_1959_, lean_object* v_____do__lift_1960_){
_start:
{
lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_box(v_enableLog_1951_);
lean_inc(v_toBind_1958_);
lean_inc(v_inst_1955_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1962_, 0, v_inst_1948_);
lean_closure_set(v___f_1962_, 1, v_____do__lift_1960_);
lean_closure_set(v___f_1962_, 2, v_id_1949_);
lean_closure_set(v___f_1962_, 3, v_toPure_1950_);
lean_closure_set(v___f_1962_, 4, v___x_1961_);
lean_closure_set(v___f_1962_, 5, v___f_1952_);
lean_closure_set(v___f_1962_, 6, v_inst_1953_);
lean_closure_set(v___f_1962_, 7, v_inst_1954_);
lean_closure_set(v___f_1962_, 8, v_inst_1955_);
lean_closure_set(v___f_1962_, 9, v_inst_1956_);
lean_closure_set(v___f_1962_, 10, v_inst_1957_);
lean_closure_set(v___f_1962_, 11, v_toBind_1958_);
lean_closure_set(v___f_1962_, 12, v_getEnv_1959_);
v___x_1963_ = lean_apply_4(v_toBind_1958_, lean_box(0), lean_box(0), v_inst_1955_, v___f_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1964_, lean_object* v_id_1965_, lean_object* v_toPure_1966_, lean_object* v_enableLog_1967_, lean_object* v___f_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_toBind_1974_, lean_object* v_getEnv_1975_, lean_object* v_____do__lift_1976_){
_start:
{
uint8_t v_enableLog_boxed_1977_; lean_object* v_res_1978_; 
v_enableLog_boxed_1977_ = lean_unbox(v_enableLog_1967_);
v_res_1978_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1964_, v_id_1965_, v_toPure_1966_, v_enableLog_boxed_1977_, v___f_1968_, v_inst_1969_, v_inst_1970_, v_inst_1971_, v_inst_1972_, v_inst_1973_, v_toBind_1974_, v_getEnv_1975_, v_____do__lift_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_id_1986_, uint8_t v_enableLog_1987_){
_start:
{
lean_object* v_toApplicative_1988_; lean_object* v_toBind_1989_; lean_object* v_getEnv_1990_; lean_object* v_toPure_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
v_toApplicative_1988_ = lean_ctor_get(v_inst_1980_, 0);
v_toBind_1989_ = lean_ctor_get(v_inst_1980_, 1);
lean_inc_n(v_toBind_1989_, 2);
v_getEnv_1990_ = lean_ctor_get(v_inst_1982_, 0);
lean_inc_n(v_getEnv_1990_, 2);
v_toPure_1991_ = lean_ctor_get(v_toApplicative_1988_, 1);
lean_inc(v_toPure_1991_);
v___f_1992_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_1993_ = lean_box(v_enableLog_1987_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1994_, 0, v_inst_1981_);
lean_closure_set(v___f_1994_, 1, v_id_1986_);
lean_closure_set(v___f_1994_, 2, v_toPure_1991_);
lean_closure_set(v___f_1994_, 3, v___x_1993_);
lean_closure_set(v___f_1994_, 4, v___f_1992_);
lean_closure_set(v___f_1994_, 5, v_inst_1980_);
lean_closure_set(v___f_1994_, 6, v_inst_1982_);
lean_closure_set(v___f_1994_, 7, v_inst_1983_);
lean_closure_set(v___f_1994_, 8, v_inst_1984_);
lean_closure_set(v___f_1994_, 9, v_inst_1985_);
lean_closure_set(v___f_1994_, 10, v_toBind_1989_);
lean_closure_set(v___f_1994_, 11, v_getEnv_1990_);
v___x_1995_ = lean_apply_4(v_toBind_1989_, lean_box(0), lean_box(0), v_getEnv_1990_, v___f_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_id_2002_, lean_object* v_enableLog_2003_){
_start:
{
uint8_t v_enableLog_boxed_2004_; lean_object* v_res_2005_; 
v_enableLog_boxed_2004_ = lean_unbox(v_enableLog_2003_);
v_res_2005_ = l_Lean_resolveGlobalName___redArg(v_inst_1996_, v_inst_1997_, v_inst_1998_, v_inst_1999_, v_inst_2000_, v_inst_2001_, v_id_2002_, v_enableLog_boxed_2004_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_id_2013_, uint8_t v_enableLog_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_resolveGlobalName___redArg(v_inst_2007_, v_inst_2008_, v_inst_2009_, v_inst_2010_, v_inst_2011_, v_inst_2012_, v_id_2013_, v_enableLog_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_id_2023_, lean_object* v_enableLog_2024_){
_start:
{
uint8_t v_enableLog_boxed_2025_; lean_object* v_res_2026_; 
v_enableLog_boxed_2025_ = lean_unbox(v_enableLog_2024_);
v_res_2026_ = l_Lean_resolveGlobalName(v_m_2016_, v_inst_2017_, v_inst_2018_, v_inst_2019_, v_inst_2020_, v_inst_2021_, v_inst_2022_, v_id_2023_, v_enableLog_boxed_2025_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2027_, lean_object* v_nss_2028_, lean_object* v_____r_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_apply_2(v_toPure_2027_, lean_box(0), v_nss_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2033_, lean_object* v_____do__lift_2034_, lean_object* v_id_2035_, uint8_t v_allowEmpty_2036_, lean_object* v_toPure_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_toBind_2040_, lean_object* v_____do__lift_2041_){
_start:
{
lean_object* v_nss_2042_; 
lean_inc(v_id_2035_);
v_nss_2042_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2033_, v_____do__lift_2034_, v_____do__lift_2041_, v_id_2035_);
if (v_allowEmpty_2036_ == 0)
{
uint8_t v___x_2043_; 
v___x_2043_ = l_List_isEmpty___redArg(v_nss_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v_toBind_2040_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
lean_dec(v_id_2035_);
v___x_2044_ = lean_apply_2(v_toPure_2037_, lean_box(0), v_nss_2042_);
return v___x_2044_;
}
else
{
lean_object* v___f_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___f_2045_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2045_, 0, v_toPure_2037_);
lean_closure_set(v___f_2045_, 1, v_nss_2042_);
v___x_2046_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2035_, v___x_2043_);
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = l_Lean_MessageData_ofFormat(v___x_2051_);
v___x_2053_ = l_Lean_throwError___redArg(v_inst_2038_, v_inst_2039_, v___x_2052_);
v___x_2054_ = lean_apply_4(v_toBind_2040_, lean_box(0), lean_box(0), v___x_2053_, v___f_2045_);
return v___x_2054_;
}
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_toBind_2040_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
lean_dec(v_id_2035_);
v___x_2055_ = lean_apply_2(v_toPure_2037_, lean_box(0), v_nss_2042_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2056_, lean_object* v_____do__lift_2057_, lean_object* v_id_2058_, lean_object* v_allowEmpty_2059_, lean_object* v_toPure_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_toBind_2063_, lean_object* v_____do__lift_2064_){
_start:
{
uint8_t v_allowEmpty_boxed_2065_; lean_object* v_res_2066_; 
v_allowEmpty_boxed_2065_ = lean_unbox(v_allowEmpty_2059_);
v_res_2066_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2056_, v_____do__lift_2057_, v_id_2058_, v_allowEmpty_boxed_2065_, v_toPure_2060_, v_inst_2061_, v_inst_2062_, v_toBind_2063_, v_____do__lift_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2067_, lean_object* v_id_2068_, uint8_t v_allowEmpty_2069_, lean_object* v_toPure_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_toBind_2073_, lean_object* v_getOpenDecls_2074_, lean_object* v_____do__lift_2075_){
_start:
{
lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(v_allowEmpty_2069_);
lean_inc(v_toBind_2073_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2077_, 0, v_____do__lift_2067_);
lean_closure_set(v___f_2077_, 1, v_____do__lift_2075_);
lean_closure_set(v___f_2077_, 2, v_id_2068_);
lean_closure_set(v___f_2077_, 3, v___x_2076_);
lean_closure_set(v___f_2077_, 4, v_toPure_2070_);
lean_closure_set(v___f_2077_, 5, v_inst_2071_);
lean_closure_set(v___f_2077_, 6, v_inst_2072_);
lean_closure_set(v___f_2077_, 7, v_toBind_2073_);
v___x_2078_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v_getOpenDecls_2074_, v___f_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2079_, lean_object* v_id_2080_, lean_object* v_allowEmpty_2081_, lean_object* v_toPure_2082_, lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_toBind_2085_, lean_object* v_getOpenDecls_2086_, lean_object* v_____do__lift_2087_){
_start:
{
uint8_t v_allowEmpty_boxed_2088_; lean_object* v_res_2089_; 
v_allowEmpty_boxed_2088_ = lean_unbox(v_allowEmpty_2081_);
v_res_2089_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2079_, v_id_2080_, v_allowEmpty_boxed_2088_, v_toPure_2082_, v_inst_2083_, v_inst_2084_, v_toBind_2085_, v_getOpenDecls_2086_, v_____do__lift_2087_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2090_, lean_object* v_id_2091_, uint8_t v_allowEmpty_2092_, lean_object* v_toPure_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_toBind_2096_, lean_object* v_____do__lift_2097_){
_start:
{
lean_object* v_getCurrNamespace_2098_; lean_object* v_getOpenDecls_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; lean_object* v___x_2102_; 
v_getCurrNamespace_2098_ = lean_ctor_get(v_inst_2090_, 0);
lean_inc(v_getCurrNamespace_2098_);
v_getOpenDecls_2099_ = lean_ctor_get(v_inst_2090_, 1);
lean_inc(v_getOpenDecls_2099_);
lean_dec_ref(v_inst_2090_);
v___x_2100_ = lean_box(v_allowEmpty_2092_);
lean_inc(v_toBind_2096_);
v___f_2101_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2101_, 0, v_____do__lift_2097_);
lean_closure_set(v___f_2101_, 1, v_id_2091_);
lean_closure_set(v___f_2101_, 2, v___x_2100_);
lean_closure_set(v___f_2101_, 3, v_toPure_2093_);
lean_closure_set(v___f_2101_, 4, v_inst_2094_);
lean_closure_set(v___f_2101_, 5, v_inst_2095_);
lean_closure_set(v___f_2101_, 6, v_toBind_2096_);
lean_closure_set(v___f_2101_, 7, v_getOpenDecls_2099_);
v___x_2102_ = lean_apply_4(v_toBind_2096_, lean_box(0), lean_box(0), v_getCurrNamespace_2098_, v___f_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2103_, lean_object* v_id_2104_, lean_object* v_allowEmpty_2105_, lean_object* v_toPure_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_toBind_2109_, lean_object* v_____do__lift_2110_){
_start:
{
uint8_t v_allowEmpty_boxed_2111_; lean_object* v_res_2112_; 
v_allowEmpty_boxed_2111_ = lean_unbox(v_allowEmpty_2105_);
v_res_2112_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2103_, v_id_2104_, v_allowEmpty_boxed_2111_, v_toPure_2106_, v_inst_2107_, v_inst_2108_, v_toBind_2109_, v_____do__lift_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_id_2117_, uint8_t v_allowEmpty_2118_){
_start:
{
lean_object* v_toApplicative_2119_; lean_object* v_toBind_2120_; lean_object* v_getEnv_2121_; lean_object* v_toPure_2122_; lean_object* v___x_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; 
v_toApplicative_2119_ = lean_ctor_get(v_inst_2113_, 0);
v_toBind_2120_ = lean_ctor_get(v_inst_2113_, 1);
lean_inc_n(v_toBind_2120_, 2);
v_getEnv_2121_ = lean_ctor_get(v_inst_2115_, 0);
lean_inc(v_getEnv_2121_);
lean_dec_ref(v_inst_2115_);
v_toPure_2122_ = lean_ctor_get(v_toApplicative_2119_, 1);
lean_inc(v_toPure_2122_);
v___x_2123_ = lean_box(v_allowEmpty_2118_);
v___f_2124_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2124_, 0, v_inst_2114_);
lean_closure_set(v___f_2124_, 1, v_id_2117_);
lean_closure_set(v___f_2124_, 2, v___x_2123_);
lean_closure_set(v___f_2124_, 3, v_toPure_2122_);
lean_closure_set(v___f_2124_, 4, v_inst_2113_);
lean_closure_set(v___f_2124_, 5, v_inst_2116_);
lean_closure_set(v___f_2124_, 6, v_toBind_2120_);
v___x_2125_ = lean_apply_4(v_toBind_2120_, lean_box(0), lean_box(0), v_getEnv_2121_, v___f_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_id_2130_, lean_object* v_allowEmpty_2131_){
_start:
{
uint8_t v_allowEmpty_boxed_2132_; lean_object* v_res_2133_; 
v_allowEmpty_boxed_2132_ = lean_unbox(v_allowEmpty_2131_);
v_res_2133_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2126_, v_inst_2127_, v_inst_2128_, v_inst_2129_, v_id_2130_, v_allowEmpty_boxed_2132_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_id_2139_, uint8_t v_allowEmpty_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2135_, v_inst_2136_, v_inst_2137_, v_inst_2138_, v_id_2139_, v_allowEmpty_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_id_2147_, lean_object* v_allowEmpty_2148_){
_start:
{
uint8_t v_allowEmpty_boxed_2149_; lean_object* v_res_2150_; 
v_allowEmpty_boxed_2149_ = lean_unbox(v_allowEmpty_2148_);
v_res_2150_ = l_Lean_resolveNamespaceCore(v_m_2142_, v_inst_2143_, v_inst_2144_, v_inst_2145_, v_inst_2146_, v_id_2147_, v_allowEmpty_boxed_2149_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
lean_object* v_ns_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_ns_2152_ = lean_ctor_get(v_x_2151_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_x_2151_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v_x_2151_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_ns_2152_);
lean_dec(v_x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set_tag(v___x_2154_, 1);
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_ns_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v___x_2160_; 
lean_dec_ref(v_x_2151_);
v___x_2160_ = lean_box(0);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2161_, lean_object* v_withRef_2162_, lean_object* v___x_2163_, lean_object* v_oldRef_2164_){
_start:
{
lean_object* v_ref_2165_; lean_object* v___x_2166_; 
v_ref_2165_ = l_Lean_replaceRef(v_x_2161_, v_oldRef_2164_);
v___x_2166_ = lean_apply_3(v_withRef_2162_, lean_box(0), v_ref_2165_, v___x_2163_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2167_, lean_object* v_withRef_2168_, lean_object* v___x_2169_, lean_object* v_oldRef_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2167_, v_withRef_2168_, v___x_2169_, v_oldRef_2170_);
lean_dec(v_oldRef_2170_);
lean_dec(v_x_2167_);
return v_res_2171_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2179_ = l_Lean_MessageData_ofFormat(v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_inst_2183_, lean_object* v_x_2184_){
_start:
{
if (lean_obj_tag(v_x_2184_) == 3)
{
lean_object* v_toApplicative_2185_; lean_object* v_toBind_2186_; lean_object* v_toPure_2187_; lean_object* v_toMonadRef_2188_; lean_object* v_val_2189_; lean_object* v_preresolved_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v_pre_2193_; uint8_t v___x_2194_; 
v_toApplicative_2185_ = lean_ctor_get(v_inst_2180_, 0);
v_toBind_2186_ = lean_ctor_get(v_inst_2180_, 1);
lean_inc(v_toBind_2186_);
v_toPure_2187_ = lean_ctor_get(v_toApplicative_2185_, 1);
v_toMonadRef_2188_ = lean_ctor_get(v_inst_2183_, 1);
v_val_2189_ = lean_ctor_get(v_x_2184_, 2);
v_preresolved_2190_ = lean_ctor_get(v_x_2184_, 3);
v___f_2191_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2192_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2190_);
v_pre_2193_ = l_List_filterMapTR_go___redArg(v___f_2191_, v_preresolved_2190_, v___x_2192_);
v___x_2194_ = l_List_isEmpty___redArg(v_pre_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_inc(v_toPure_2187_);
lean_dec(v_toBind_2186_);
lean_dec_ref_known(v_x_2184_, 4);
lean_dec_ref(v_inst_2183_);
lean_dec_ref(v_inst_2182_);
lean_dec_ref(v_inst_2181_);
lean_dec_ref(v_inst_2180_);
v___x_2195_ = lean_apply_2(v_toPure_2187_, lean_box(0), v_pre_2193_);
return v___x_2195_;
}
else
{
lean_object* v_getRef_2196_; lean_object* v_withRef_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___f_2200_; lean_object* v___x_2201_; 
lean_dec(v_pre_2193_);
v_getRef_2196_ = lean_ctor_get(v_toMonadRef_2188_, 0);
lean_inc(v_getRef_2196_);
v_withRef_2197_ = lean_ctor_get(v_toMonadRef_2188_, 1);
lean_inc(v_withRef_2197_);
v___x_2198_ = 0;
lean_inc(v_val_2189_);
v___x_2199_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2180_, v_inst_2181_, v_inst_2182_, v_inst_2183_, v_val_2189_, v___x_2198_);
v___f_2200_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2200_, 0, v_x_2184_);
lean_closure_set(v___f_2200_, 1, v_withRef_2197_);
lean_closure_set(v___f_2200_, 2, v___x_2199_);
v___x_2201_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v_getRef_2196_, v___f_2200_);
return v___x_2201_;
}
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec_ref(v_inst_2182_);
lean_dec_ref(v_inst_2181_);
v___x_2202_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2203_ = l_Lean_throwErrorAt___redArg(v_inst_2180_, v_inst_2183_, v_x_2184_, v___x_2202_);
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_resolveNamespace___redArg(v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_, v_x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2213_, lean_object* v___f_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_toPure_2217_, lean_object* v_____do__lift_2218_){
_start:
{
if (lean_obj_tag(v_____do__lift_2218_) == 1)
{
lean_object* v_tail_2234_; 
v_tail_2234_ = lean_ctor_get(v_____do__lift_2218_, 1);
if (lean_obj_tag(v_tail_2234_) == 0)
{
lean_object* v_head_2235_; lean_object* v___x_2236_; 
lean_dec_ref(v_inst_2216_);
lean_dec_ref(v_inst_2215_);
lean_dec_ref(v___f_2214_);
v_head_2235_ = lean_ctor_get(v_____do__lift_2218_, 0);
lean_inc(v_head_2235_);
lean_dec_ref_known(v_____do__lift_2218_, 2);
v___x_2236_ = lean_apply_2(v_toPure_2217_, lean_box(0), v_head_2235_);
return v___x_2236_;
}
else
{
lean_dec(v_toPure_2217_);
goto v___jp_2219_;
}
}
else
{
lean_dec(v_toPure_2217_);
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2220_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2221_ = l_Lean_TSyntax_getId(v_id_2213_);
v___x_2222_ = 1;
v___x_2223_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2221_, v___x_2222_);
v___x_2224_ = lean_string_append(v___x_2220_, v___x_2223_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2226_ = lean_string_append(v___x_2224_, v___x_2225_);
v___x_2227_ = l_List_toString___redArg(v___f_2214_, v_____do__lift_2218_);
v___x_2228_ = lean_string_append(v___x_2226_, v___x_2227_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2230_ = lean_string_append(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
v___x_2232_ = l_Lean_MessageData_ofFormat(v___x_2231_);
v___x_2233_ = l_Lean_throwError___redArg(v_inst_2215_, v_inst_2216_, v___x_2232_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2237_, lean_object* v___f_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_toPure_2241_, lean_object* v_____do__lift_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2237_, v___f_2238_, v_inst_2239_, v_inst_2240_, v_toPure_2241_, v_____do__lift_2242_);
lean_dec(v_id_2237_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_id_2249_){
_start:
{
lean_object* v_toApplicative_2250_; lean_object* v_toBind_2251_; lean_object* v_toPure_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___f_2255_; lean_object* v___x_2256_; 
v_toApplicative_2250_ = lean_ctor_get(v_inst_2245_, 0);
v_toBind_2251_ = lean_ctor_get(v_inst_2245_, 1);
lean_inc(v_toBind_2251_);
v_toPure_2252_ = lean_ctor_get(v_toApplicative_2250_, 1);
lean_inc(v_toPure_2252_);
v___f_2253_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2249_);
lean_inc_ref(v_inst_2248_);
lean_inc_ref(v_inst_2245_);
v___x_2254_ = l_Lean_resolveNamespace___redArg(v_inst_2245_, v_inst_2246_, v_inst_2247_, v_inst_2248_, v_id_2249_);
v___f_2255_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2255_, 0, v_id_2249_);
lean_closure_set(v___f_2255_, 1, v___f_2253_);
lean_closure_set(v___f_2255_, 2, v_inst_2245_);
lean_closure_set(v___f_2255_, 3, v_inst_2248_);
lean_closure_set(v___f_2255_, 4, v_toPure_2252_);
v___x_2256_ = lean_apply_4(v_toBind_2251_, lean_box(0), lean_box(0), v___x_2254_, v___f_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_id_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2258_, v_inst_2259_, v_inst_2260_, v_inst_2261_, v_id_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2264_){
_start:
{
lean_object* v_snd_2265_; uint8_t v___x_2266_; 
v_snd_2265_ = lean_ctor_get(v_x_2264_, 1);
v___x_2266_ = l_List_isEmpty___redArg(v_snd_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2267_){
_start:
{
uint8_t v_res_2268_; lean_object* v_r_2269_; 
v_res_2268_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2267_);
lean_dec_ref(v_x_2267_);
v_r_2269_ = lean_box(v_res_2268_);
return v_r_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2270_){
_start:
{
lean_object* v_fst_2271_; 
v_fst_2271_ = lean_ctor_get(v_x_2270_, 0);
lean_inc(v_fst_2271_);
return v_fst_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2272_);
lean_dec_ref(v_x_2272_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2274_, lean_object* v_cs_2275_, lean_object* v_toPure_2276_, lean_object* v_____r_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = l_List_mapTR_loop___redArg(v___f_2274_, v_cs_2275_, v___x_2278_);
v___x_2280_ = lean_apply_2(v_toPure_2276_, lean_box(0), v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2281_, lean_object* v_____r_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_apply_1(v___f_2281_, v_____r_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_n_2287_, lean_object* v_toBind_2288_, lean_object* v___f_2289_, lean_object* v_____do__lift_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2284_, v_inst_2285_, v_inst_2286_, v_____do__lift_2290_, v_n_2287_);
v___x_2292_ = lean_apply_4(v_toBind_2288_, lean_box(0), lean_box(0), v___x_2291_, v___f_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_n_2298_, lean_object* v_cs_2299_){
_start:
{
lean_object* v_toApplicative_2300_; lean_object* v_toBind_2301_; lean_object* v_toPure_2302_; lean_object* v_toMonadRef_2303_; lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; lean_object* v_cs_2307_; lean_object* v___f_2308_; uint8_t v___x_2309_; 
v_toApplicative_2300_ = lean_ctor_get(v_inst_2295_, 0);
v_toBind_2301_ = lean_ctor_get(v_inst_2295_, 1);
lean_inc(v_toBind_2301_);
v_toPure_2302_ = lean_ctor_get(v_toApplicative_2300_, 1);
v_toMonadRef_2303_ = lean_ctor_get(v_inst_2297_, 1);
v___f_2304_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2305_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2306_ = lean_box(0);
v_cs_2307_ = l_List_filterTR_loop___redArg(v___f_2304_, v_cs_2299_, v___x_2306_);
lean_inc(v_toPure_2302_);
lean_inc(v_cs_2307_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2308_, 0, v___f_2305_);
lean_closure_set(v___f_2308_, 1, v_cs_2307_);
lean_closure_set(v___f_2308_, 2, v_toPure_2302_);
v___x_2309_ = l_List_isEmpty___redArg(v_cs_2307_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_inc(v_toPure_2302_);
lean_dec_ref(v___f_2308_);
lean_dec(v_toBind_2301_);
lean_dec(v_n_2298_);
lean_dec_ref(v_inst_2297_);
lean_dec_ref(v_inst_2296_);
lean_dec_ref(v_inst_2295_);
v___x_2310_ = lean_box(0);
v___x_2311_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2305_, v_cs_2307_, v_toPure_2302_, v___x_2310_);
return v___x_2311_;
}
else
{
lean_object* v_getRef_2312_; lean_object* v___f_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; 
lean_dec(v_cs_2307_);
v_getRef_2312_ = lean_ctor_get(v_toMonadRef_2303_, 0);
lean_inc(v_getRef_2312_);
v___f_2313_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2313_, 0, v___f_2308_);
lean_inc(v_toBind_2301_);
v___f_2314_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2314_, 0, v_inst_2295_);
lean_closure_set(v___f_2314_, 1, v_inst_2296_);
lean_closure_set(v___f_2314_, 2, v_inst_2297_);
lean_closure_set(v___f_2314_, 3, v_n_2298_);
lean_closure_set(v___f_2314_, 4, v_toBind_2301_);
lean_closure_set(v___f_2314_, 5, v___f_2313_);
v___x_2315_ = lean_apply_4(v_toBind_2301_, lean_box(0), lean_box(0), v_getRef_2312_, v___f_2314_);
return v___x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_n_2320_, lean_object* v_cs_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_filterFieldList___redArg(v_inst_2317_, v_inst_2318_, v_inst_2319_, v_n_2320_, v_cs_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_n_2326_, lean_object* v_cs_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_filterFieldList___redArg(v_inst_2323_, v_inst_2324_, v_inst_2325_, v_n_2326_, v_cs_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_n_2336_){
_start:
{
lean_object* v_toBind_2337_; lean_object* v___f_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_toBind_2337_ = lean_ctor_get(v_inst_2329_, 1);
lean_inc(v_toBind_2337_);
lean_inc(v_n_2336_);
lean_inc_ref(v_inst_2331_);
lean_inc_ref(v_inst_2329_);
v___f_2338_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2338_, 0, v_inst_2329_);
lean_closure_set(v___f_2338_, 1, v_inst_2331_);
lean_closure_set(v___f_2338_, 2, v_inst_2335_);
lean_closure_set(v___f_2338_, 3, v_n_2336_);
v___x_2339_ = 1;
v___x_2340_ = l_Lean_resolveGlobalName___redArg(v_inst_2329_, v_inst_2330_, v_inst_2331_, v_inst_2332_, v_inst_2333_, v_inst_2334_, v_n_2336_, v___x_2339_);
v___x_2341_ = lean_apply_4(v_toBind_2337_, lean_box(0), lean_box(0), v___x_2340_, v___f_2338_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_n_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2343_, v_inst_2344_, v_inst_2345_, v_inst_2346_, v_inst_2347_, v_inst_2348_, v_inst_2349_, v_n_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2352_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_box(0);
v___x_2354_ = l_Lean_mkConst(v_declName_2352_, v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2358_ = l_Lean_stringToMessageData(v___x_2357_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_n_2365_, lean_object* v_cs_2366_){
_start:
{
lean_object* v_toApplicative_2367_; lean_object* v_toPure_2368_; lean_object* v___f_2369_; 
v_toApplicative_2367_ = lean_ctor_get(v_inst_2363_, 0);
v_toPure_2368_ = lean_ctor_get(v_toApplicative_2367_, 1);
v___f_2369_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2366_) == 1)
{
lean_object* v_tail_2383_; 
v_tail_2383_ = lean_ctor_get(v_cs_2366_, 1);
if (lean_obj_tag(v_tail_2383_) == 0)
{
lean_object* v_head_2384_; lean_object* v___x_2385_; 
lean_inc(v_toPure_2368_);
lean_dec(v_n_2365_);
lean_dec_ref(v_inst_2364_);
lean_dec_ref(v_inst_2363_);
v_head_2384_ = lean_ctor_get(v_cs_2366_, 0);
lean_inc(v_head_2384_);
lean_dec_ref_known(v_cs_2366_, 2);
v___x_2385_ = lean_apply_2(v_toPure_2368_, lean_box(0), v_head_2384_);
return v___x_2385_;
}
else
{
goto v___jp_2370_;
}
}
else
{
goto v___jp_2370_;
}
v___jp_2370_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2371_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2372_ = l_Lean_MessageData_ofName(v_n_2365_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_box(0);
v___x_2377_ = l_List_mapTR_loop___redArg(v___f_2369_, v_cs_2366_, v___x_2376_);
v___x_2378_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2379_ = l_List_mapTR_loop___redArg(v___x_2378_, v___x_2377_, v___x_2376_);
v___x_2380_ = l_Lean_MessageData_ofList(v___x_2379_);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2375_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = l_Lean_throwError___redArg(v_inst_2363_, v_inst_2364_, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2386_, lean_object* v_inst_2387_, lean_object* v_inst_2388_, lean_object* v_n_2389_, lean_object* v_cs_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_ensureNoOverload___redArg(v_inst_2387_, v_inst_2388_, v_n_2389_, v_cs_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_n_2394_, lean_object* v_____do__lift_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_ensureNoOverload___redArg(v_inst_2392_, v_inst_2393_, v_n_2394_, v_____do__lift_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_n_2404_){
_start:
{
lean_object* v_toBind_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_toBind_2405_ = lean_ctor_get(v_inst_2397_, 1);
lean_inc(v_toBind_2405_);
lean_inc(v_n_2404_);
lean_inc_ref(v_inst_2403_);
lean_inc_ref(v_inst_2397_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2406_, 0, v_inst_2397_);
lean_closure_set(v___f_2406_, 1, v_inst_2403_);
lean_closure_set(v___f_2406_, 2, v_n_2404_);
v___x_2407_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2397_, v_inst_2398_, v_inst_2399_, v_inst_2400_, v_inst_2401_, v_inst_2402_, v_inst_2403_, v_n_2404_);
v___x_2408_ = lean_apply_4(v_toBind_2405_, lean_box(0), lean_box(0), v___x_2407_, v___f_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_n_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2410_, v_inst_2411_, v_inst_2412_, v_inst_2413_, v_inst_2414_, v_inst_2415_, v_inst_2416_, v_n_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2419_){
_start:
{
if (lean_obj_tag(v_x_2419_) == 1)
{
lean_object* v_fields_2420_; 
v_fields_2420_ = lean_ctor_get(v_x_2419_, 1);
if (lean_obj_tag(v_fields_2420_) == 0)
{
lean_object* v_n_2421_; lean_object* v___x_2422_; 
v_n_2421_ = lean_ctor_get(v_x_2419_, 0);
lean_inc(v_n_2421_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_n_2421_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_box(0);
return v___x_2423_;
}
}
else
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_box(0);
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2425_);
lean_dec_ref(v_x_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2427_, lean_object* v_withRef_2428_, lean_object* v___x_2429_, lean_object* v_oldRef_2430_){
_start:
{
lean_object* v_ref_2431_; lean_object* v___x_2432_; 
v_ref_2431_ = l_Lean_replaceRef(v_stx_2427_, v_oldRef_2430_);
v___x_2432_ = lean_apply_3(v_withRef_2428_, lean_box(0), v_ref_2431_, v___x_2429_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2433_, lean_object* v_withRef_2434_, lean_object* v___x_2435_, lean_object* v_oldRef_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2433_, v_withRef_2434_, v___x_2435_, v_oldRef_2436_);
lean_dec(v_oldRef_2436_);
lean_dec(v_stx_2433_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_stx_2441_, lean_object* v_k_2442_){
_start:
{
if (lean_obj_tag(v_stx_2441_) == 3)
{
lean_object* v_toApplicative_2443_; lean_object* v_toBind_2444_; lean_object* v_toPure_2445_; lean_object* v_toMonadRef_2446_; lean_object* v_val_2447_; lean_object* v_preresolved_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; lean_object* v_pre_2451_; uint8_t v___x_2452_; 
v_toApplicative_2443_ = lean_ctor_get(v_inst_2439_, 0);
lean_inc_ref(v_toApplicative_2443_);
v_toBind_2444_ = lean_ctor_get(v_inst_2439_, 1);
lean_inc(v_toBind_2444_);
lean_dec_ref(v_inst_2439_);
v_toPure_2445_ = lean_ctor_get(v_toApplicative_2443_, 1);
lean_inc(v_toPure_2445_);
lean_dec_ref(v_toApplicative_2443_);
v_toMonadRef_2446_ = lean_ctor_get(v_inst_2440_, 1);
lean_inc_ref(v_toMonadRef_2446_);
lean_dec_ref(v_inst_2440_);
v_val_2447_ = lean_ctor_get(v_stx_2441_, 2);
v_preresolved_2448_ = lean_ctor_get(v_stx_2441_, 3);
v___f_2449_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2450_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2448_);
v_pre_2451_ = l_List_filterMapTR_go___redArg(v___f_2449_, v_preresolved_2448_, v___x_2450_);
v___x_2452_ = l_List_isEmpty___redArg(v_pre_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
lean_dec_ref(v_toMonadRef_2446_);
lean_dec(v_toBind_2444_);
lean_dec_ref_known(v_stx_2441_, 4);
lean_dec(v_k_2442_);
v___x_2453_ = lean_apply_2(v_toPure_2445_, lean_box(0), v_pre_2451_);
return v___x_2453_;
}
else
{
lean_object* v_getRef_2454_; lean_object* v_withRef_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; 
lean_dec(v_pre_2451_);
lean_dec(v_toPure_2445_);
v_getRef_2454_ = lean_ctor_get(v_toMonadRef_2446_, 0);
lean_inc(v_getRef_2454_);
v_withRef_2455_ = lean_ctor_get(v_toMonadRef_2446_, 1);
lean_inc(v_withRef_2455_);
lean_dec_ref(v_toMonadRef_2446_);
lean_inc(v_val_2447_);
v___x_2456_ = lean_apply_1(v_k_2442_, v_val_2447_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2457_, 0, v_stx_2441_);
lean_closure_set(v___f_2457_, 1, v_withRef_2455_);
lean_closure_set(v___f_2457_, 2, v___x_2456_);
v___x_2458_ = lean_apply_4(v_toBind_2444_, lean_box(0), lean_box(0), v_getRef_2454_, v___f_2457_);
return v___x_2458_;
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec(v_k_2442_);
v___x_2459_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2460_ = l_Lean_throwErrorAt___redArg(v_inst_2439_, v_inst_2440_, v_stx_2441_, v___x_2459_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_stx_2464_, lean_object* v_k_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2462_, v_inst_2463_, v_stx_2464_, v_k_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_stx_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_inc_ref(v_inst_2473_);
lean_inc_ref(v_inst_2467_);
v___x_2475_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2475_, 0, lean_box(0));
lean_closure_set(v___x_2475_, 1, v_inst_2467_);
lean_closure_set(v___x_2475_, 2, v_inst_2468_);
lean_closure_set(v___x_2475_, 3, v_inst_2469_);
lean_closure_set(v___x_2475_, 4, v_inst_2470_);
lean_closure_set(v___x_2475_, 5, v_inst_2471_);
lean_closure_set(v___x_2475_, 6, v_inst_2472_);
lean_closure_set(v___x_2475_, 7, v_inst_2473_);
v___x_2476_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2467_, v_inst_2473_, v_stx_2474_, v___x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_stx_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_resolveGlobalConst___redArg(v_inst_2478_, v_inst_2479_, v_inst_2480_, v_inst_2481_, v_inst_2482_, v_inst_2483_, v_inst_2484_, v_stx_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2488_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2489_ = lean_unsigned_to_nat(11u);
v___x_2490_ = lean_unsigned_to_nat(429u);
v___x_2491_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2492_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2493_ = l_mkPanicMessageWithDecl(v___x_2492_, v___x_2491_, v___x_2490_, v___x_2489_, v___x_2488_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_id_2499_, lean_object* v_cs_2500_){
_start:
{
if (lean_obj_tag(v_cs_2500_) == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_id_2499_);
lean_dec_ref(v_inst_2498_);
v___x_2501_ = lean_box(0);
v___x_2502_ = l_instInhabitedOfMonad___redArg(v_inst_2497_, v___x_2501_);
v___x_2503_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2504_ = l_panic___redArg(v___x_2502_, v___x_2503_);
lean_dec(v___x_2502_);
return v___x_2504_;
}
else
{
lean_object* v_tail_2505_; 
v_tail_2505_ = lean_ctor_get(v_cs_2500_, 1);
if (lean_obj_tag(v_tail_2505_) == 0)
{
lean_object* v_toApplicative_2506_; lean_object* v_toPure_2507_; lean_object* v_head_2508_; lean_object* v___x_2509_; 
v_toApplicative_2506_ = lean_ctor_get(v_inst_2497_, 0);
lean_inc_ref(v_toApplicative_2506_);
lean_dec(v_id_2499_);
lean_dec_ref(v_inst_2498_);
lean_dec_ref(v_inst_2497_);
v_toPure_2507_ = lean_ctor_get(v_toApplicative_2506_, 1);
lean_inc(v_toPure_2507_);
lean_dec_ref(v_toApplicative_2506_);
v_head_2508_ = lean_ctor_get(v_cs_2500_, 0);
lean_inc(v_head_2508_);
lean_dec_ref_known(v_cs_2500_, 2);
v___x_2509_ = lean_apply_2(v_toPure_2507_, lean_box(0), v_head_2508_);
return v___x_2509_;
}
else
{
lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___f_2510_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2511_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2512_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2513_ = lean_box(0);
v___x_2514_ = 0;
lean_inc(v_id_2499_);
v___x_2515_ = l_Lean_Syntax_formatStx(v_id_2499_, v___x_2513_, v___x_2514_);
v___x_2516_ = l_Std_Format_defWidth;
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = l_Std_Format_pretty(v___x_2515_, v___x_2516_, v___x_2517_, v___x_2517_);
v___x_2519_ = lean_string_append(v___x_2512_, v___x_2518_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2521_ = lean_string_append(v___x_2519_, v___x_2520_);
v___x_2522_ = lean_box(0);
v___x_2523_ = l_List_mapTR_loop___redArg(v___f_2510_, v_cs_2500_, v___x_2522_);
v___x_2524_ = l_List_toString___redArg(v___x_2511_, v___x_2523_);
v___x_2525_ = lean_string_append(v___x_2521_, v___x_2524_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
v___x_2527_ = l_Lean_MessageData_ofFormat(v___x_2526_);
v___x_2528_ = l_Lean_throwErrorAt___redArg(v_inst_2497_, v_inst_2498_, v_id_2499_, v___x_2527_);
return v___x_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_id_2532_, lean_object* v_cs_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2530_, v_inst_2531_, v_id_2532_, v_cs_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_id_2537_, lean_object* v_____do__lift_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2535_, v_inst_2536_, v_id_2537_, v_____do__lift_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_id_2547_){
_start:
{
lean_object* v_toBind_2548_; lean_object* v___f_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_toBind_2548_ = lean_ctor_get(v_inst_2540_, 1);
lean_inc(v_toBind_2548_);
lean_inc(v_id_2547_);
lean_inc_ref(v_inst_2546_);
lean_inc_ref(v_inst_2540_);
v___f_2549_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2549_, 0, v_inst_2540_);
lean_closure_set(v___f_2549_, 1, v_inst_2546_);
lean_closure_set(v___f_2549_, 2, v_id_2547_);
v___x_2550_ = l_Lean_resolveGlobalConst___redArg(v_inst_2540_, v_inst_2541_, v_inst_2542_, v_inst_2543_, v_inst_2544_, v_inst_2545_, v_inst_2546_, v_id_2547_);
v___x_2551_ = lean_apply_4(v_toBind_2548_, lean_box(0), lean_box(0), v___x_2550_, v___f_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_id_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2553_, v_inst_2554_, v_inst_2555_, v_inst_2556_, v_inst_2557_, v_inst_2558_, v_inst_2559_, v_id_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2562_, lean_object* v___f_2563_, uint8_t v_globalDeclFoundNext_2564_, uint8_t v_globalDeclFound_2565_, lean_object* v_r_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v_r_2568_; uint8_t v___x_2569_; 
v___x_2567_ = lean_box(0);
v_r_2568_ = l_List_filterTR_loop___redArg(v___f_2562_, v_r_2566_, v___x_2567_);
v___x_2569_ = l_List_isEmpty___redArg(v_r_2568_);
lean_dec(v_r_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_box(v_globalDeclFoundNext_2564_);
v___x_2572_ = lean_apply_2(v___f_2563_, v___x_2570_, v___x_2571_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_box(v_globalDeclFound_2565_);
v___x_2575_ = lean_apply_2(v___f_2563_, v___x_2573_, v___x_2574_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2576_, lean_object* v___f_2577_, lean_object* v_globalDeclFoundNext_2578_, lean_object* v_globalDeclFound_2579_, lean_object* v_r_2580_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2581_; uint8_t v_globalDeclFound_boxed_2582_; lean_object* v_res_2583_; 
v_globalDeclFoundNext_boxed_2581_ = lean_unbox(v_globalDeclFoundNext_2578_);
v_globalDeclFound_boxed_2582_ = lean_unbox(v_globalDeclFound_2579_);
v_res_2583_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2576_, v___f_2577_, v_globalDeclFoundNext_boxed_2581_, v_globalDeclFound_boxed_2582_, v_r_2580_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2584_, lean_object* v_projs_2585_, lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_view_2592_, lean_object* v_findLocalDecl_x3f_2593_, lean_object* v_pre_2594_, lean_object* v_____r_2595_, lean_object* v_globalDeclFoundNext_2596_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2597_; lean_object* v_res_2598_; 
v_globalDeclFoundNext_boxed_2597_ = lean_unbox(v_globalDeclFoundNext_2596_);
v_res_2598_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2584_, v_projs_2585_, v_inst_2586_, v_inst_2587_, v_inst_2588_, v_inst_2589_, v_inst_2590_, v_inst_2591_, v_view_2592_, v_findLocalDecl_x3f_2593_, v_pre_2594_, v_____r_2595_, v_globalDeclFoundNext_boxed_2597_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2599_, lean_object* v_inst_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_view_2605_, lean_object* v_findLocalDecl_x3f_2606_, lean_object* v_n_2607_, lean_object* v_projs_2608_, uint8_t v_globalDeclFound_2609_){
_start:
{
lean_object* v_toApplicative_2610_; lean_object* v_imported_2611_; lean_object* v_ctx_2612_; lean_object* v_scopes_2613_; lean_object* v_toBind_2614_; lean_object* v_toPure_2615_; lean_object* v___f_2616_; lean_object* v_givenNameView_2617_; uint8_t v___y_2619_; 
v_toApplicative_2610_ = lean_ctor_get(v_inst_2599_, 0);
v_imported_2611_ = lean_ctor_get(v_view_2605_, 1);
v_ctx_2612_ = lean_ctor_get(v_view_2605_, 2);
v_scopes_2613_ = lean_ctor_get(v_view_2605_, 3);
v_toBind_2614_ = lean_ctor_get(v_inst_2599_, 1);
v_toPure_2615_ = lean_ctor_get(v_toApplicative_2610_, 1);
v___f_2616_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2613_);
lean_inc(v_ctx_2612_);
lean_inc(v_imported_2611_);
lean_inc(v_n_2607_);
v_givenNameView_2617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2617_, 0, v_n_2607_);
lean_ctor_set(v_givenNameView_2617_, 1, v_imported_2611_);
lean_ctor_set(v_givenNameView_2617_, 2, v_ctx_2612_);
lean_ctor_set(v_givenNameView_2617_, 3, v_scopes_2613_);
if (v_globalDeclFound_2609_ == 0)
{
v___y_2619_ = v_globalDeclFound_2609_;
goto v___jp_2618_;
}
else
{
uint8_t v___x_2655_; 
v___x_2655_ = l_List_isEmpty___redArg(v_projs_2608_);
if (v___x_2655_ == 0)
{
v___y_2619_ = v_globalDeclFound_2609_;
goto v___jp_2618_;
}
else
{
uint8_t v___x_2656_; 
v___x_2656_ = 0;
v___y_2619_ = v___x_2656_;
goto v___jp_2618_;
}
}
v___jp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_box(v___y_2619_);
lean_inc_ref(v_findLocalDecl_x3f_2606_);
lean_inc_ref(v_givenNameView_2617_);
v___x_2621_ = lean_apply_2(v_findLocalDecl_x3f_2606_, v_givenNameView_2617_, v___x_2620_);
if (lean_obj_tag(v___x_2621_) == 0)
{
if (lean_obj_tag(v_n_2607_) == 1)
{
lean_object* v_pre_2622_; lean_object* v_str_2623_; lean_object* v___f_2624_; 
v_pre_2622_ = lean_ctor_get(v_n_2607_, 0);
lean_inc_n(v_pre_2622_, 2);
v_str_2623_ = lean_ctor_get(v_n_2607_, 1);
lean_inc_ref_n(v_str_2623_, 2);
lean_dec_ref_known(v_n_2607_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2606_);
lean_inc_ref(v_view_2605_);
lean_inc(v_inst_2604_);
lean_inc_ref(v_inst_2603_);
lean_inc(v_inst_2602_);
lean_inc_ref(v_inst_2601_);
lean_inc_ref(v_inst_2600_);
lean_inc_ref(v_inst_2599_);
lean_inc(v_projs_2608_);
v___f_2624_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2624_, 0, v_str_2623_);
lean_closure_set(v___f_2624_, 1, v_projs_2608_);
lean_closure_set(v___f_2624_, 2, v_inst_2599_);
lean_closure_set(v___f_2624_, 3, v_inst_2600_);
lean_closure_set(v___f_2624_, 4, v_inst_2601_);
lean_closure_set(v___f_2624_, 5, v_inst_2602_);
lean_closure_set(v___f_2624_, 6, v_inst_2603_);
lean_closure_set(v___f_2624_, 7, v_inst_2604_);
lean_closure_set(v___f_2624_, 8, v_view_2605_);
lean_closure_set(v___f_2624_, 9, v_findLocalDecl_x3f_2606_);
lean_closure_set(v___f_2624_, 10, v_pre_2622_);
if (v_globalDeclFound_2609_ == 0)
{
uint8_t v_globalDeclFoundNext_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_inc(v_toBind_2614_);
lean_dec_ref(v_str_2623_);
lean_dec(v_pre_2622_);
lean_dec(v_projs_2608_);
lean_dec_ref(v_findLocalDecl_x3f_2606_);
lean_dec_ref(v_view_2605_);
v_globalDeclFoundNext_2625_ = 1;
v___x_2626_ = lean_box(v_globalDeclFoundNext_2625_);
v___x_2627_ = lean_box(v_globalDeclFound_2609_);
v___f_2628_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2628_, 0, v___f_2616_);
lean_closure_set(v___f_2628_, 1, v___f_2624_);
lean_closure_set(v___f_2628_, 2, v___x_2626_);
lean_closure_set(v___f_2628_, 3, v___x_2627_);
v___x_2629_ = l_Lean_MacroScopesView_review(v_givenNameView_2617_);
v___x_2630_ = l_Lean_resolveGlobalName___redArg(v_inst_2599_, v_inst_2600_, v_inst_2601_, v_inst_2602_, v_inst_2603_, v_inst_2604_, v___x_2629_, v_globalDeclFound_2609_);
v___x_2631_ = lean_apply_4(v_toBind_2614_, lean_box(0), lean_box(0), v___x_2630_, v___f_2628_);
return v___x_2631_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec_ref(v___f_2624_);
lean_dec_ref_known(v_givenNameView_2617_, 4);
v___x_2632_ = lean_box(0);
v___x_2633_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2623_, v_projs_2608_, v_inst_2599_, v_inst_2600_, v_inst_2601_, v_inst_2602_, v_inst_2603_, v_inst_2604_, v_view_2605_, v_findLocalDecl_x3f_2606_, v_pre_2622_, v___x_2632_, v_globalDeclFound_2609_);
return v___x_2633_;
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc(v_toPure_2615_);
lean_dec_ref_known(v_givenNameView_2617_, 4);
lean_dec(v_projs_2608_);
lean_dec(v_n_2607_);
lean_dec_ref(v_findLocalDecl_x3f_2606_);
lean_dec_ref(v_view_2605_);
lean_dec(v_inst_2604_);
lean_dec_ref(v_inst_2603_);
lean_dec(v_inst_2602_);
lean_dec_ref(v_inst_2601_);
lean_dec_ref(v_inst_2600_);
lean_dec_ref(v_inst_2599_);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_apply_2(v_toPure_2615_, lean_box(0), v___x_2634_);
return v___x_2635_;
}
}
else
{
lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2652_; 
lean_inc(v_toPure_2615_);
lean_dec_ref_known(v_givenNameView_2617_, 4);
lean_dec(v_n_2607_);
lean_dec_ref(v_findLocalDecl_x3f_2606_);
lean_dec_ref(v_view_2605_);
lean_dec(v_inst_2604_);
lean_dec_ref(v_inst_2603_);
lean_dec(v_inst_2602_);
lean_dec_ref(v_inst_2601_);
lean_dec_ref(v_inst_2600_);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_inst_2599_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; lean_object* v_unused_2654_; 
v_unused_2653_ = lean_ctor_get(v_inst_2599_, 1);
lean_dec(v_unused_2653_);
v_unused_2654_ = lean_ctor_get(v_inst_2599_, 0);
lean_dec(v_unused_2654_);
v___x_2637_ = v_inst_2599_;
v_isShared_2638_ = v_isSharedCheck_2652_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v_inst_2599_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2652_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_val_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2651_; 
v_val_2639_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2641_ = v___x_2621_;
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_val_2639_);
lean_dec(v___x_2621_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = l_Lean_LocalDecl_toExpr(v_val_2639_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 1, v_projs_2608_);
lean_ctor_set(v___x_2637_, 0, v___x_2643_);
v___x_2645_ = v___x_2637_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_projs_2608_);
v___x_2645_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2647_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2645_);
v___x_2647_ = v___x_2641_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_apply_2(v_toPure_2615_, lean_box(0), v___x_2647_);
return v___x_2648_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2657_, lean_object* v_projs_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_view_2665_, lean_object* v_findLocalDecl_x3f_2666_, lean_object* v_pre_2667_, lean_object* v_____r_2668_, uint8_t v_globalDeclFoundNext_2669_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_str_2657_);
lean_ctor_set(v___x_2670_, 1, v_projs_2658_);
v___x_2671_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2659_, v_inst_2660_, v_inst_2661_, v_inst_2662_, v_inst_2663_, v_inst_2664_, v_view_2665_, v_findLocalDecl_x3f_2666_, v_pre_2667_, v___x_2670_, v_globalDeclFoundNext_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_view_2678_, lean_object* v_findLocalDecl_x3f_2679_, lean_object* v_n_2680_, lean_object* v_projs_2681_, lean_object* v_globalDeclFound_2682_){
_start:
{
uint8_t v_globalDeclFound_boxed_2683_; lean_object* v_res_2684_; 
v_globalDeclFound_boxed_2683_ = lean_unbox(v_globalDeclFound_2682_);
v_res_2684_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2672_, v_inst_2673_, v_inst_2674_, v_inst_2675_, v_inst_2676_, v_inst_2677_, v_view_2678_, v_findLocalDecl_x3f_2679_, v_n_2680_, v_projs_2681_, v_globalDeclFound_boxed_2683_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_view_2692_, lean_object* v_findLocalDecl_x3f_2693_, lean_object* v_n_2694_, lean_object* v_projs_2695_, uint8_t v_globalDeclFound_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_inst_2689_, v_inst_2690_, v_inst_2691_, v_view_2692_, v_findLocalDecl_x3f_2693_, v_n_2694_, v_projs_2695_, v_globalDeclFound_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_view_2705_, lean_object* v_findLocalDecl_x3f_2706_, lean_object* v_n_2707_, lean_object* v_projs_2708_, lean_object* v_globalDeclFound_2709_){
_start:
{
uint8_t v_globalDeclFound_boxed_2710_; lean_object* v_res_2711_; 
v_globalDeclFound_boxed_2710_ = lean_unbox(v_globalDeclFound_2709_);
v_res_2711_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_inst_2703_, v_inst_2704_, v_view_2705_, v_findLocalDecl_x3f_2706_, v_n_2707_, v_projs_2708_, v_globalDeclFound_boxed_2710_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2712_, lean_object* v_givenNameView_2713_, lean_object* v_fullDeclName_2714_, lean_object* v_ns_2715_){
_start:
{
lean_object* v_name_2716_; lean_object* v_imported_2717_; lean_object* v_ctx_2718_; lean_object* v_scopes_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v_name_2716_ = lean_ctor_get(v_givenNameView_2713_, 0);
v_imported_2717_ = lean_ctor_get(v_givenNameView_2713_, 1);
v_ctx_2718_ = lean_ctor_get(v_givenNameView_2713_, 2);
v_scopes_2719_ = lean_ctor_get(v_givenNameView_2713_, 3);
lean_inc(v_name_2716_);
lean_inc(v_ns_2715_);
v___x_2720_ = l_Lean_Name_append(v_ns_2715_, v_name_2716_);
lean_inc(v_scopes_2719_);
lean_inc(v_ctx_2718_);
lean_inc(v_imported_2717_);
v___x_2721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v_imported_2717_);
lean_ctor_set(v___x_2721_, 2, v_ctx_2718_);
lean_ctor_set(v___x_2721_, 3, v_scopes_2719_);
v___x_2722_ = l_Lean_MacroScopesView_review(v___x_2721_);
v___x_2723_ = lean_name_eq(v___x_2722_, v_fullDeclName_2714_);
lean_dec(v___x_2722_);
if (v___x_2723_ == 0)
{
if (lean_obj_tag(v_ns_2715_) == 1)
{
lean_object* v_pre_2724_; 
v_pre_2724_ = lean_ctor_get(v_ns_2715_, 0);
lean_inc(v_pre_2724_);
lean_dec_ref_known(v_ns_2715_, 2);
v_ns_2715_ = v_pre_2724_;
goto _start;
}
else
{
lean_object* v___x_2726_; 
lean_dec(v_ns_2715_);
lean_dec_ref(v_givenNameView_2713_);
lean_dec_ref(v_localDecl_2712_);
v___x_2726_ = lean_box(0);
return v___x_2726_;
}
}
else
{
lean_object* v___x_2727_; 
lean_dec(v_ns_2715_);
lean_dec_ref(v_givenNameView_2713_);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_localDecl_2712_);
return v___x_2727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2728_, lean_object* v_givenNameView_2729_, lean_object* v_fullDeclName_2730_, lean_object* v_ns_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2728_, v_givenNameView_2729_, v_fullDeclName_2730_, v_ns_2731_);
lean_dec(v_fullDeclName_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2733_, lean_object* v_givenName_2734_){
_start:
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = l_Lean_LocalDecl_userName(v_localDecl_2733_);
v___x_2736_ = lean_name_eq(v___x_2735_, v_givenName_2734_);
lean_dec(v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; 
lean_dec_ref(v_localDecl_2733_);
v___x_2737_ = lean_box(0);
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_localDecl_2733_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2739_, lean_object* v_givenName_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2739_, v_givenName_2740_);
lean_dec(v_givenName_2740_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2742_, lean_object* v_givenName_2743_, uint8_t v_skipAuxDecl_2744_, lean_object* v___f_2745_, lean_object* v_auxDeclToFullName_2746_, lean_object* v_currNamespace_2747_, lean_object* v_givenNameView_2748_, lean_object* v_x_2749_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
lean_dec_ref(v_givenNameView_2748_);
lean_dec(v_currNamespace_2747_);
lean_dec(v_auxDeclToFullName_2746_);
lean_dec_ref(v___f_2745_);
lean_dec(v_givenName_2743_);
lean_dec_ref(v_matchLocalDecl_x3f_2742_);
return v_x_2749_;
}
else
{
lean_object* v_val_2750_; uint8_t v___x_2751_; 
v_val_2750_ = lean_ctor_get(v_x_2749_, 0);
v___x_2751_ = l_Lean_LocalDecl_isAuxDecl(v_val_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_inc(v_val_2750_);
lean_dec_ref_known(v_x_2749_, 1);
lean_dec_ref(v_givenNameView_2748_);
lean_dec(v_currNamespace_2747_);
lean_dec(v_auxDeclToFullName_2746_);
lean_dec_ref(v___f_2745_);
v___x_2752_ = lean_apply_2(v_matchLocalDecl_x3f_2742_, v_val_2750_, v_givenName_2743_);
return v___x_2752_;
}
else
{
if (v_skipAuxDecl_2744_ == 0)
{
if (v___x_2751_ == 0)
{
lean_object* v___x_2753_; 
lean_dec_ref_known(v_x_2749_, 1);
lean_dec_ref(v_givenNameView_2748_);
lean_dec(v_currNamespace_2747_);
lean_dec(v_auxDeclToFullName_2746_);
lean_dec_ref(v___f_2745_);
lean_dec(v_givenName_2743_);
lean_dec_ref(v_matchLocalDecl_x3f_2742_);
v___x_2753_ = lean_box(0);
return v___x_2753_;
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = l_Lean_LocalDecl_fvarId(v_val_2750_);
v___x_2755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2745_, v_auxDeclToFullName_2746_, v___x_2754_);
if (lean_obj_tag(v___x_2755_) == 1)
{
lean_object* v_val_2756_; lean_object* v_fullDeclView_2757_; lean_object* v___y_2759_; lean_object* v_name_2780_; lean_object* v___x_2781_; 
lean_dec(v_givenName_2743_);
lean_dec_ref(v_matchLocalDecl_x3f_2742_);
v_val_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v_fullDeclView_2757_ = l_Lean_extractMacroScopes(v_val_2756_);
v_name_2780_ = lean_ctor_get(v_fullDeclView_2757_, 0);
lean_inc_n(v_name_2780_, 2);
v___x_2781_ = l_Lean_privateToUserName_x3f(v_name_2780_);
if (lean_obj_tag(v___x_2781_) == 0)
{
v___y_2759_ = v_name_2780_;
goto v___jp_2758_;
}
else
{
lean_object* v_val_2782_; 
lean_dec(v_name_2780_);
v_val_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_val_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___y_2759_ = v_val_2782_;
goto v___jp_2758_;
}
v___jp_2758_:
{
lean_object* v_imported_2760_; lean_object* v_ctx_2761_; lean_object* v_scopes_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2778_; 
v_imported_2760_ = lean_ctor_get(v_fullDeclView_2757_, 1);
v_ctx_2761_ = lean_ctor_get(v_fullDeclView_2757_, 2);
v_scopes_2762_ = lean_ctor_get(v_fullDeclView_2757_, 3);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_fullDeclView_2757_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; 
v_unused_2779_ = lean_ctor_get(v_fullDeclView_2757_, 0);
lean_dec(v_unused_2779_);
v___x_2764_ = v_fullDeclView_2757_;
v_isShared_2765_ = v_isSharedCheck_2778_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_scopes_2762_);
lean_inc(v_ctx_2761_);
lean_inc(v_imported_2760_);
lean_dec(v_fullDeclView_2757_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2778_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_fullDeclView_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___y_2759_);
v_fullDeclView_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___y_2759_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_imported_2760_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_ctx_2761_);
lean_ctor_set(v_reuseFailAlloc_2777_, 3, v_scopes_2762_);
v_fullDeclView_2767_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v_fullDeclName_2768_; uint8_t v___x_2769_; 
lean_inc_ref(v_fullDeclView_2767_);
v_fullDeclName_2768_ = l_Lean_MacroScopesView_review(v_fullDeclView_2767_);
v___x_2769_ = l_Lean_Name_isPrefixOf(v_currNamespace_2747_, v_fullDeclName_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_inc(v_val_2750_);
lean_dec_ref(v_fullDeclView_2767_);
lean_dec_ref_known(v_x_2749_, 1);
v___x_2770_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2750_, v_givenNameView_2748_, v_fullDeclName_2768_, v_currNamespace_2747_);
lean_dec(v_fullDeclName_2768_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v_localDeclNameView_2772_; uint8_t v___x_2773_; 
lean_dec(v_fullDeclName_2768_);
lean_dec(v_currNamespace_2747_);
v___x_2771_ = l_Lean_LocalDecl_userName(v_val_2750_);
v_localDeclNameView_2772_ = l_Lean_extractMacroScopes(v___x_2771_);
v___x_2773_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2772_, v_givenNameView_2748_);
lean_dec_ref(v_localDeclNameView_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
lean_dec_ref(v_fullDeclView_2767_);
lean_dec_ref_known(v_x_2749_, 1);
lean_dec_ref(v_givenNameView_2748_);
v___x_2774_ = lean_box(0);
return v___x_2774_;
}
else
{
uint8_t v___x_2775_; 
v___x_2775_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2748_, v_fullDeclView_2767_);
lean_dec_ref(v_fullDeclView_2767_);
lean_dec_ref(v_givenNameView_2748_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; 
lean_dec_ref_known(v_x_2749_, 1);
v___x_2776_ = lean_box(0);
return v___x_2776_;
}
else
{
return v_x_2749_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2783_; 
lean_inc(v_val_2750_);
lean_dec(v___x_2755_);
lean_dec_ref_known(v_x_2749_, 1);
lean_dec_ref(v_givenNameView_2748_);
lean_dec(v_currNamespace_2747_);
v___x_2783_ = lean_apply_2(v_matchLocalDecl_x3f_2742_, v_val_2750_, v_givenName_2743_);
return v___x_2783_;
}
}
}
else
{
lean_object* v___x_2784_; 
lean_dec_ref_known(v_x_2749_, 1);
lean_dec_ref(v_givenNameView_2748_);
lean_dec(v_currNamespace_2747_);
lean_dec(v_auxDeclToFullName_2746_);
lean_dec_ref(v___f_2745_);
lean_dec(v_givenName_2743_);
lean_dec_ref(v_matchLocalDecl_x3f_2742_);
v___x_2784_ = lean_box(0);
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2785_, lean_object* v_givenName_2786_, lean_object* v_skipAuxDecl_2787_, lean_object* v___f_2788_, lean_object* v_auxDeclToFullName_2789_, lean_object* v_currNamespace_2790_, lean_object* v_givenNameView_2791_, lean_object* v_x_2792_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2793_; lean_object* v_res_2794_; 
v_skipAuxDecl_boxed_2793_ = lean_unbox(v_skipAuxDecl_2787_);
v_res_2794_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2785_, v_givenName_2786_, v_skipAuxDecl_boxed_2793_, v___f_2788_, v_auxDeclToFullName_2789_, v_currNamespace_2790_, v_givenNameView_2791_, v_x_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2795_, lean_object* v_matchLocalDecl_x3f_2796_, lean_object* v_givenName_2797_, lean_object* v_x_2798_){
_start:
{
if (lean_obj_tag(v_x_2798_) == 0)
{
lean_dec(v_givenName_2797_);
lean_dec_ref(v_matchLocalDecl_x3f_2796_);
return v_x_2798_;
}
else
{
lean_object* v_val_2799_; uint8_t v___x_2800_; 
v_val_2799_ = lean_ctor_get(v_x_2798_, 0);
lean_inc(v_val_2799_);
lean_dec_ref_known(v_x_2798_, 1);
v___x_2800_ = l_Lean_LocalDecl_isAuxDecl(v_val_2799_);
if (v___x_2800_ == 0)
{
lean_dec(v_val_2799_);
lean_dec(v_givenName_2797_);
lean_dec_ref(v_matchLocalDecl_x3f_2796_);
lean_inc(v_localDecl_x3f_2795_);
return v_localDecl_x3f_2795_;
}
else
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_apply_2(v_matchLocalDecl_x3f_2796_, v_val_2799_, v_givenName_2797_);
return v___x_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2802_, lean_object* v_matchLocalDecl_x3f_2803_, lean_object* v_givenName_2804_, lean_object* v_x_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2802_, v_matchLocalDecl_x3f_2803_, v_givenName_2804_, v_x_2805_);
lean_dec(v_localDecl_x3f_2802_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2826_, lean_object* v_matchLocalDecl_x3f_2827_, lean_object* v___f_2828_, lean_object* v_auxDeclToFullName_2829_, lean_object* v_currNamespace_2830_, lean_object* v_givenNameView_2831_, uint8_t v_skipAuxDecl_2832_){
_start:
{
lean_object* v_decls_2833_; lean_object* v_givenName_2834_; lean_object* v___x_2835_; lean_object* v___f_2836_; lean_object* v___x_2837_; lean_object* v_localDecl_x3f_2838_; 
v_decls_2833_ = lean_ctor_get(v_lctx_2826_, 1);
lean_inc_ref_n(v_decls_2833_, 2);
lean_dec_ref(v_lctx_2826_);
lean_inc_ref(v_givenNameView_2831_);
v_givenName_2834_ = l_Lean_MacroScopesView_review(v_givenNameView_2831_);
v___x_2835_ = lean_box(v_skipAuxDecl_2832_);
lean_inc(v_givenName_2834_);
lean_inc_ref(v_matchLocalDecl_x3f_2827_);
v___f_2836_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2836_, 0, v_matchLocalDecl_x3f_2827_);
lean_closure_set(v___f_2836_, 1, v_givenName_2834_);
lean_closure_set(v___f_2836_, 2, v___x_2835_);
lean_closure_set(v___f_2836_, 3, v___f_2828_);
lean_closure_set(v___f_2836_, 4, v_auxDeclToFullName_2829_);
lean_closure_set(v___f_2836_, 5, v_currNamespace_2830_);
lean_closure_set(v___f_2836_, 6, v_givenNameView_2831_);
v___x_2837_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2838_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2837_, v_decls_2833_, v___f_2836_);
if (lean_obj_tag(v_localDecl_x3f_2838_) == 0)
{
if (v_skipAuxDecl_2832_ == 0)
{
lean_object* v___f_2839_; lean_object* v___x_2840_; 
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2839_, 0, v_localDecl_x3f_2838_);
lean_closure_set(v___f_2839_, 1, v_matchLocalDecl_x3f_2827_);
lean_closure_set(v___f_2839_, 2, v_givenName_2834_);
v___x_2840_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2837_, v_decls_2833_, v___f_2839_);
return v___x_2840_;
}
else
{
lean_dec(v_givenName_2834_);
lean_dec_ref(v_decls_2833_);
lean_dec_ref(v_matchLocalDecl_x3f_2827_);
return v_localDecl_x3f_2838_;
}
}
else
{
lean_dec(v_givenName_2834_);
lean_dec_ref(v_decls_2833_);
lean_dec_ref(v_matchLocalDecl_x3f_2827_);
return v_localDecl_x3f_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2841_, lean_object* v_matchLocalDecl_x3f_2842_, lean_object* v___f_2843_, lean_object* v_auxDeclToFullName_2844_, lean_object* v_currNamespace_2845_, lean_object* v_givenNameView_2846_, lean_object* v_skipAuxDecl_2847_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2848_; lean_object* v_res_2849_; 
v_skipAuxDecl_boxed_2848_ = lean_unbox(v_skipAuxDecl_2847_);
v_res_2849_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2841_, v_matchLocalDecl_x3f_2842_, v___f_2843_, v_auxDeclToFullName_2844_, v_currNamespace_2845_, v_givenNameView_2846_, v_skipAuxDecl_boxed_2848_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2850_, lean_object* v_lctx_2851_, lean_object* v_matchLocalDecl_x3f_2852_, lean_object* v___f_2853_, lean_object* v_auxDeclToFullName_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_currNamespace_2861_){
_start:
{
lean_object* v_view_2862_; lean_object* v_name_2863_; lean_object* v_findLocalDecl_x3f_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; 
v_view_2862_ = l_Lean_extractMacroScopes(v_n_2850_);
v_name_2863_ = lean_ctor_get(v_view_2862_, 0);
lean_inc(v_name_2863_);
v_findLocalDecl_x3f_2864_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2864_, 0, v_lctx_2851_);
lean_closure_set(v_findLocalDecl_x3f_2864_, 1, v_matchLocalDecl_x3f_2852_);
lean_closure_set(v_findLocalDecl_x3f_2864_, 2, v___f_2853_);
lean_closure_set(v_findLocalDecl_x3f_2864_, 3, v_auxDeclToFullName_2854_);
lean_closure_set(v_findLocalDecl_x3f_2864_, 4, v_currNamespace_2861_);
v___x_2865_ = lean_box(0);
v___x_2866_ = 0;
v___x_2867_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2855_, v_inst_2856_, v_inst_2857_, v_inst_2858_, v_inst_2859_, v_inst_2860_, v_view_2862_, v_findLocalDecl_x3f_2864_, v_name_2863_, v___x_2865_, v___x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2868_, lean_object* v_n_2869_, lean_object* v_lctx_2870_, lean_object* v_matchLocalDecl_x3f_2871_, lean_object* v___f_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_toBind_2878_, lean_object* v_____do__lift_2879_){
_start:
{
lean_object* v_auxDeclToFullName_2880_; lean_object* v_getCurrNamespace_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; 
v_auxDeclToFullName_2880_ = lean_ctor_get(v_____do__lift_2879_, 2);
lean_inc(v_auxDeclToFullName_2880_);
lean_dec_ref(v_____do__lift_2879_);
v_getCurrNamespace_2881_ = lean_ctor_get(v_inst_2868_, 0);
lean_inc(v_getCurrNamespace_2881_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2882_, 0, v_n_2869_);
lean_closure_set(v___f_2882_, 1, v_lctx_2870_);
lean_closure_set(v___f_2882_, 2, v_matchLocalDecl_x3f_2871_);
lean_closure_set(v___f_2882_, 3, v___f_2872_);
lean_closure_set(v___f_2882_, 4, v_auxDeclToFullName_2880_);
lean_closure_set(v___f_2882_, 5, v_inst_2873_);
lean_closure_set(v___f_2882_, 6, v_inst_2868_);
lean_closure_set(v___f_2882_, 7, v_inst_2874_);
lean_closure_set(v___f_2882_, 8, v_inst_2875_);
lean_closure_set(v___f_2882_, 9, v_inst_2876_);
lean_closure_set(v___f_2882_, 10, v_inst_2877_);
v___x_2883_ = lean_apply_4(v_toBind_2878_, lean_box(0), lean_box(0), v_getCurrNamespace_2881_, v___f_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2884_, lean_object* v_n_2885_, lean_object* v_matchLocalDecl_x3f_2886_, lean_object* v___f_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_toBind_2893_, lean_object* v_inst_2894_, lean_object* v_lctx_2895_){
_start:
{
lean_object* v___f_2896_; lean_object* v___x_2897_; 
lean_inc(v_toBind_2893_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2896_, 0, v_inst_2884_);
lean_closure_set(v___f_2896_, 1, v_n_2885_);
lean_closure_set(v___f_2896_, 2, v_lctx_2895_);
lean_closure_set(v___f_2896_, 3, v_matchLocalDecl_x3f_2886_);
lean_closure_set(v___f_2896_, 4, v___f_2887_);
lean_closure_set(v___f_2896_, 5, v_inst_2888_);
lean_closure_set(v___f_2896_, 6, v_inst_2889_);
lean_closure_set(v___f_2896_, 7, v_inst_2890_);
lean_closure_set(v___f_2896_, 8, v_inst_2891_);
lean_closure_set(v___f_2896_, 9, v_inst_2892_);
lean_closure_set(v___f_2896_, 10, v_toBind_2893_);
v___x_2897_ = lean_apply_4(v_toBind_2893_, lean_box(0), lean_box(0), v_inst_2894_, v___f_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2900_, lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_n_2907_){
_start:
{
lean_object* v_toBind_2908_; lean_object* v___f_2909_; lean_object* v_matchLocalDecl_x3f_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; 
v_toBind_2908_ = lean_ctor_get(v_inst_2900_, 1);
lean_inc_n(v_toBind_2908_, 2);
v___f_2909_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2910_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2906_);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2911_, 0, v_inst_2901_);
lean_closure_set(v___f_2911_, 1, v_n_2907_);
lean_closure_set(v___f_2911_, 2, v_matchLocalDecl_x3f_2910_);
lean_closure_set(v___f_2911_, 3, v___f_2909_);
lean_closure_set(v___f_2911_, 4, v_inst_2900_);
lean_closure_set(v___f_2911_, 5, v_inst_2902_);
lean_closure_set(v___f_2911_, 6, v_inst_2903_);
lean_closure_set(v___f_2911_, 7, v_inst_2904_);
lean_closure_set(v___f_2911_, 8, v_inst_2905_);
lean_closure_set(v___f_2911_, 9, v_toBind_2908_);
lean_closure_set(v___f_2911_, 10, v_inst_2906_);
v___x_2912_ = lean_apply_4(v_toBind_2908_, lean_box(0), lean_box(0), v_inst_2906_, v___f_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2913_, lean_object* v_inst_2914_, lean_object* v_inst_2915_, lean_object* v_inst_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_n_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_resolveLocalName___redArg(v_inst_2914_, v_inst_2915_, v_inst_2916_, v_inst_2917_, v_inst_2918_, v_inst_2919_, v_inst_2920_, v_n_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2923_, uint8_t v_____do__lift_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_box(v_____do__lift_2924_);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
v___x_2927_ = lean_apply_2(v_toPure_2923_, lean_box(0), v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2928_, lean_object* v_____do__lift_2929_){
_start:
{
uint8_t v_____do__lift_1062__boxed_2930_; lean_object* v_res_2931_; 
v_____do__lift_1062__boxed_2930_ = lean_unbox(v_____do__lift_2929_);
v_res_2931_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2928_, v_____do__lift_1062__boxed_2930_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2932_, lean_object* v___y_2933_, lean_object* v_____do__lift_2934_){
_start:
{
if (lean_obj_tag(v_____do__lift_2934_) == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec(v___y_2933_);
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_2935_);
return v___x_2936_;
}
else
{
lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_isSharedCheck_2944_ = !lean_is_exclusive(v_____do__lift_2934_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_____do__lift_2934_, 0);
lean_dec(v_unused_2945_);
v___x_2938_ = v_____do__lift_2934_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_dec(v_____do__lift_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___y_2933_);
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___y_2933_);
v___x_2941_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_2941_);
return v___x_2942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2948_, lean_object* v_toBind_2949_, lean_object* v___f_2950_, lean_object* v_____do__lift_2951_){
_start:
{
if (lean_obj_tag(v_____do__lift_2951_) == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
lean_dec(v___f_2950_);
lean_dec(v_toBind_2949_);
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_apply_2(v_toPure_2948_, lean_box(0), v___x_2952_);
return v___x_2953_;
}
else
{
lean_object* v_val_2954_; uint8_t v___x_2955_; 
v_val_2954_ = lean_ctor_get(v_____do__lift_2951_, 0);
v___x_2955_ = lean_unbox(v_val_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_apply_2(v_toPure_2948_, lean_box(0), v___x_2956_);
v___x_2958_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2957_, v___f_2950_);
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2960_ = lean_apply_2(v_toPure_2948_, lean_box(0), v___x_2959_);
v___x_2961_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2960_, v___f_2950_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2962_, lean_object* v_toBind_2963_, lean_object* v___f_2964_, lean_object* v_____do__lift_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2962_, v_toBind_2963_, v___f_2964_, v_____do__lift_2965_);
lean_dec(v_____do__lift_2965_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2967_, lean_object* v_filter_2968_, lean_object* v___y_2969_, lean_object* v_toBind_2970_, lean_object* v___f_2971_, lean_object* v___f_2972_, lean_object* v_____do__lift_2973_){
_start:
{
if (lean_obj_tag(v_____do__lift_2973_) == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v___f_2972_);
lean_dec(v___f_2971_);
lean_dec(v_toBind_2970_);
lean_dec(v___y_2969_);
lean_dec(v_filter_2968_);
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_apply_2(v_toPure_2967_, lean_box(0), v___x_2974_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec(v_toPure_2967_);
v___x_2976_ = lean_apply_1(v_filter_2968_, v___y_2969_);
lean_inc(v_toBind_2970_);
v___x_2977_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2976_, v___f_2971_);
v___x_2978_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2977_, v___f_2972_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_2979_, lean_object* v_filter_2980_, lean_object* v___y_2981_, lean_object* v_toBind_2982_, lean_object* v___f_2983_, lean_object* v___f_2984_, lean_object* v_____do__lift_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_2979_, v_filter_2980_, v___y_2981_, v_toBind_2982_, v___f_2983_, v___f_2984_, v_____do__lift_2985_);
lean_dec(v_____do__lift_2985_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_2987_, lean_object* v_n_u2080_2988_, lean_object* v_toBind_2989_, lean_object* v___f_2990_, lean_object* v_____do__lift_2991_){
_start:
{
if (lean_obj_tag(v_____do__lift_2991_) == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v___f_2990_);
lean_dec(v_toBind_2989_);
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_2995_);
return v___x_2996_;
}
else
{
lean_object* v_val_2997_; 
v_val_2997_ = lean_ctor_get(v_____do__lift_2991_, 0);
if (lean_obj_tag(v_val_2997_) == 1)
{
lean_object* v_tail_2998_; 
v_tail_2998_ = lean_ctor_get(v_val_2997_, 1);
if (lean_obj_tag(v_tail_2998_) == 0)
{
lean_object* v_head_2999_; lean_object* v_fst_3000_; uint8_t v___x_3001_; 
v_head_2999_ = lean_ctor_get(v_val_2997_, 0);
v_fst_3000_ = lean_ctor_get(v_head_2999_, 0);
v___x_3001_ = lean_name_eq(v_fst_3000_, v_n_u2080_2988_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_3002_);
v___x_3004_ = lean_apply_4(v_toBind_2989_, lean_box(0), lean_box(0), v___x_3003_, v___f_2990_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3006_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_3005_);
v___x_3007_ = lean_apply_4(v_toBind_2989_, lean_box(0), lean_box(0), v___x_3006_, v___f_2990_);
return v___x_3007_;
}
}
else
{
lean_dec(v___f_2990_);
lean_dec(v_toBind_2989_);
goto v___jp_2992_;
}
}
else
{
lean_dec(v___f_2990_);
lean_dec(v_toBind_2989_);
goto v___jp_2992_;
}
}
v___jp_2992_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_2993_);
return v___x_2994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3008_, lean_object* v_n_u2080_3009_, lean_object* v_toBind_3010_, lean_object* v___f_3011_, lean_object* v_____do__lift_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3008_, v_n_u2080_3009_, v_toBind_3010_, v___f_3011_, v_____do__lift_3012_);
lean_dec(v_____do__lift_3012_);
lean_dec(v_n_u2080_3009_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_n_u2080_3020_, lean_object* v_filter_3021_, lean_object* v_view_x3f_3022_, lean_object* v_n_3023_){
_start:
{
lean_object* v___f_3024_; lean_object* v___f_3025_; lean_object* v___f_3026_; lean_object* v___f_3027_; lean_object* v___f_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v_toApplicative_3036_; lean_object* v_getEnv_3037_; lean_object* v_modifyEnv_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3076_; 
lean_inc_ref_n(v_inst_3014_, 8);
v___f_3024_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3024_, 0, v_inst_3014_);
v___f_3025_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3025_, 0, v_inst_3014_);
v___f_3026_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3026_, 0, v_inst_3014_);
v___f_3027_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3027_, 0, v_inst_3014_);
v___f_3028_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3028_, 0, v_inst_3014_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___f_3024_);
lean_ctor_set(v___x_3029_, 1, v___f_3025_);
v___x_3030_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3030_, 0, lean_box(0));
lean_closure_set(v___x_3030_, 1, v_inst_3014_);
v___x_3031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
lean_ctor_set(v___x_3031_, 2, v___f_3026_);
lean_ctor_set(v___x_3031_, 3, v___f_3027_);
lean_ctor_set(v___x_3031_, 4, v___f_3028_);
v___x_3032_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3032_, 0, lean_box(0));
lean_closure_set(v___x_3032_, 1, v_inst_3014_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3034_, 0, lean_box(0));
lean_closure_set(v___x_3034_, 1, v_inst_3014_);
lean_inc_ref(v___x_3034_);
v___x_3035_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3034_, v_inst_3015_);
v_toApplicative_3036_ = lean_ctor_get(v_inst_3014_, 0);
lean_inc_ref(v_toApplicative_3036_);
v_getEnv_3037_ = lean_ctor_get(v_inst_3016_, 0);
v_modifyEnv_3038_ = lean_ctor_get(v_inst_3016_, 1);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_inst_3016_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3040_ = v_inst_3016_;
v_isShared_3041_ = v_isSharedCheck_3076_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_modifyEnv_3038_);
lean_inc(v_getEnv_3037_);
lean_dec(v_inst_3016_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3076_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_toBind_3042_; lean_object* v_toPure_3043_; lean_object* v___f_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v_toBind_3042_ = lean_ctor_get(v_inst_3014_, 1);
lean_inc_n(v_toBind_3042_, 2);
lean_dec_ref(v_inst_3014_);
v_toPure_3043_ = lean_ctor_get(v_toApplicative_3036_, 1);
lean_inc_n(v_toPure_3043_, 3);
lean_dec_ref(v_toApplicative_3036_);
lean_inc_ref(v___x_3034_);
v___f_3044_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3044_, 0, v_modifyEnv_3038_);
lean_closure_set(v___f_3044_, 1, v___x_3034_);
v___f_3045_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3045_, 0, v_toPure_3043_);
v___f_3046_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3046_, 0, v_toPure_3043_);
lean_inc_ref(v___f_3046_);
v___x_3047_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v_getEnv_3037_, v___f_3046_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 1, v___f_3044_);
lean_ctor_set(v___x_3040_, 0, v___x_3047_);
v___x_3049_ = v___x_3040_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v___f_3044_);
v___x_3049_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___f_3052_; lean_object* v___y_3054_; 
lean_inc(v_toBind_3042_);
v___x_3050_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v_inst_3017_, v___f_3046_);
lean_inc_ref(v___x_3034_);
v___x_3051_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3034_, v_inst_3018_);
v___f_3052_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3052_, 0, v_inst_3019_);
lean_closure_set(v___f_3052_, 1, v___x_3034_);
if (lean_obj_tag(v_view_x3f_3022_) == 1)
{
lean_object* v_val_3062_; lean_object* v_imported_3063_; lean_object* v_ctx_3064_; lean_object* v_scopes_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3073_; 
v_val_3062_ = lean_ctor_get(v_view_x3f_3022_, 0);
lean_inc(v_val_3062_);
lean_dec_ref_known(v_view_x3f_3022_, 1);
v_imported_3063_ = lean_ctor_get(v_val_3062_, 1);
v_ctx_3064_ = lean_ctor_get(v_val_3062_, 2);
v_scopes_3065_ = lean_ctor_get(v_val_3062_, 3);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_val_3062_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v_val_3062_, 0);
lean_dec(v_unused_3074_);
v___x_3067_ = v_val_3062_;
v_isShared_3068_ = v_isSharedCheck_3073_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_scopes_3065_);
lean_inc(v_ctx_3064_);
lean_inc(v_imported_3063_);
lean_dec(v_val_3062_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3073_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 0, v_n_3023_);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_n_3023_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_imported_3063_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ctx_3064_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_scopes_3065_);
v___x_3070_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_MacroScopesView_review(v___x_3070_);
v___y_3054_ = v___x_3071_;
goto v___jp_3053_;
}
}
}
else
{
lean_dec(v_view_x3f_3022_);
v___y_3054_ = v_n_3023_;
goto v___jp_3053_;
}
v___jp_3053_:
{
lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___f_3057_; lean_object* v___f_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
lean_inc_n(v___y_3054_, 2);
lean_inc_n(v_toPure_3043_, 3);
v___f_3055_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3055_, 0, v_toPure_3043_);
lean_closure_set(v___f_3055_, 1, v___y_3054_);
lean_inc_n(v_toBind_3042_, 3);
v___f_3056_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3056_, 0, v_toPure_3043_);
lean_closure_set(v___f_3056_, 1, v_toBind_3042_);
lean_closure_set(v___f_3056_, 2, v___f_3055_);
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3057_, 0, v_toPure_3043_);
lean_closure_set(v___f_3057_, 1, v_filter_3021_);
lean_closure_set(v___f_3057_, 2, v___y_3054_);
lean_closure_set(v___f_3057_, 3, v_toBind_3042_);
lean_closure_set(v___f_3057_, 4, v___f_3045_);
lean_closure_set(v___f_3057_, 5, v___f_3056_);
v___f_3058_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3058_, 0, v_toPure_3043_);
lean_closure_set(v___f_3058_, 1, v_n_u2080_3020_);
lean_closure_set(v___f_3058_, 2, v_toBind_3042_);
lean_closure_set(v___f_3058_, 3, v___f_3057_);
v___x_3059_ = 0;
v___x_3060_ = l_Lean_resolveGlobalName___redArg(v___x_3033_, v___x_3035_, v___x_3049_, v___x_3050_, v___x_3051_, v___f_3052_, v___y_3054_, v___x_3059_);
v___x_3061_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v___x_3060_, v___f_3058_);
return v___x_3061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3077_, lean_object* v_inst_3078_, lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_inst_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_n_u2080_3084_, lean_object* v_filter_3085_, lean_object* v_view_x3f_3086_, lean_object* v_n_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3078_, v_inst_3079_, v_inst_3080_, v_inst_3081_, v_inst_3082_, v_inst_3083_, v_n_u2080_3084_, v_filter_3085_, v_view_x3f_3086_, v_n_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3093_, lean_object* v_____x_3094_){
_start:
{
if (lean_obj_tag(v_____x_3094_) == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3096_ = lean_apply_2(v_toPure_3093_, lean_box(0), v___x_3095_);
return v___x_3096_;
}
else
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_apply_2(v_toPure_3093_, lean_box(0), v_____x_3094_);
return v___x_3097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3098_, lean_object* v_____do__lift_3099_){
_start:
{
if (lean_obj_tag(v_____do__lift_3099_) == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_apply_2(v_toPure_3098_, lean_box(0), v___x_3100_);
return v___x_3101_;
}
else
{
lean_object* v_val_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3111_; 
v_val_3102_ = lean_ctor_get(v_____do__lift_3099_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_____do__lift_3099_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3104_ = v_____do__lift_3099_;
v_isShared_3105_ = v_isSharedCheck_3111_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_val_3102_);
lean_dec(v_____do__lift_3099_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3111_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_val_3102_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3106_);
v___x_3108_ = v___x_3104_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_apply_2(v_toPure_3098_, lean_box(0), v___x_3108_);
return v___x_3109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3112_, lean_object* v___x_3113_, lean_object* v_____do__lift_3114_){
_start:
{
if (lean_obj_tag(v_____do__lift_3114_) == 0)
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_apply_2(v_toPure_3112_, lean_box(0), v___x_3113_);
return v___x_3115_;
}
else
{
lean_object* v_val_3116_; lean_object* v_fst_3117_; lean_object* v___x_3118_; 
lean_dec(v___x_3113_);
v_val_3116_ = lean_ctor_get(v_____do__lift_3114_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v_____do__lift_3114_, 1);
v_fst_3117_ = lean_ctor_get(v_val_3116_, 0);
lean_inc(v_fst_3117_);
lean_dec(v_val_3116_);
v___x_3118_ = lean_apply_2(v_toPure_3112_, lean_box(0), v_fst_3117_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3119_, lean_object* v___x_3120_, lean_object* v___x_3121_, lean_object* v_____do__lift_3122_){
_start:
{
if (lean_obj_tag(v_____do__lift_3122_) == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_dec(v___x_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v___x_3124_ = lean_apply_2(v_toPure_3119_, lean_box(0), v___x_3123_);
return v___x_3124_;
}
else
{
lean_object* v_val_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3156_; 
v_val_3125_ = lean_ctor_get(v_____do__lift_3122_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_____do__lift_3122_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3127_ = v_____do__lift_3122_;
v_isShared_3128_ = v_isSharedCheck_3156_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_val_3125_);
lean_dec(v_____do__lift_3122_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3156_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
if (lean_obj_tag(v_val_3125_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___x_3121_);
v_a_3129_ = lean_ctor_get(v_val_3125_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_val_3125_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3131_ = v_val_3125_;
v_isShared_3132_ = v_isSharedCheck_3142_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v_val_3125_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3142_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v_a_3129_);
v___x_3134_ = v___x_3127_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3120_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3135_);
v___x_3137_ = v___x_3131_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
v___x_3139_ = lean_apply_2(v_toPure_3119_, lean_box(0), v___x_3138_);
return v___x_3139_;
}
}
}
}
else
{
lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3154_; 
v_isSharedCheck_3154_ = !lean_is_exclusive(v_val_3125_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v_val_3125_, 0);
lean_dec(v_unused_3155_);
v___x_3144_ = v_val_3125_;
v_isShared_3145_ = v_isSharedCheck_3154_;
goto v_resetjp_3143_;
}
else
{
lean_dec(v_val_3125_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3154_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3121_);
lean_ctor_set(v___x_3146_, 1, v___x_3120_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3146_);
v___x_3148_ = v___x_3144_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3150_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3148_);
v___x_3150_ = v___x_3127_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_apply_2(v_toPure_3119_, lean_box(0), v___x_3150_);
return v___x_3151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3157_, lean_object* v___x_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_n_u2080_3165_, lean_object* v_filter_3166_, lean_object* v_view_x3f_3167_, lean_object* v_toBind_3168_, lean_object* v___f_3169_, lean_object* v___f_3170_, lean_object* v_a_3171_, lean_object* v_x_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_snd_3174_; lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_snd_3174_ = lean_ctor_get(v___y_3173_, 1);
lean_inc(v_snd_3174_);
lean_dec_ref(v___y_3173_);
v___x_3175_ = l_Lean_Name_appendCore(v_a_3171_, v_snd_3174_);
lean_inc(v___x_3175_);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3176_, 0, v_toPure_3157_);
lean_closure_set(v___f_3176_, 1, v___x_3175_);
lean_closure_set(v___f_3176_, 2, v___x_3158_);
v___x_3177_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3159_, v_inst_3160_, v_inst_3161_, v_inst_3162_, v_inst_3163_, v_inst_3164_, v_n_u2080_3165_, v_filter_3166_, v_view_x3f_3167_, v___x_3175_);
lean_inc_n(v_toBind_3168_, 2);
v___x_3178_ = lean_apply_4(v_toBind_3168_, lean_box(0), lean_box(0), v___x_3177_, v___f_3169_);
v___x_3179_ = lean_apply_4(v_toBind_3168_, lean_box(0), lean_box(0), v___x_3178_, v___f_3170_);
v___x_3180_ = lean_apply_4(v_toBind_3168_, lean_box(0), lean_box(0), v___x_3179_, v___f_3176_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3181_ = _args[0];
lean_object* v___x_3182_ = _args[1];
lean_object* v_inst_3183_ = _args[2];
lean_object* v_inst_3184_ = _args[3];
lean_object* v_inst_3185_ = _args[4];
lean_object* v_inst_3186_ = _args[5];
lean_object* v_inst_3187_ = _args[6];
lean_object* v_inst_3188_ = _args[7];
lean_object* v_n_u2080_3189_ = _args[8];
lean_object* v_filter_3190_ = _args[9];
lean_object* v_view_x3f_3191_ = _args[10];
lean_object* v_toBind_3192_ = _args[11];
lean_object* v___f_3193_ = _args[12];
lean_object* v___f_3194_ = _args[13];
lean_object* v_a_3195_ = _args[14];
lean_object* v_x_3196_ = _args[15];
lean_object* v___y_3197_ = _args[16];
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3181_, v___x_3182_, v_inst_3183_, v_inst_3184_, v_inst_3185_, v_inst_3186_, v_inst_3187_, v_inst_3188_, v_n_u2080_3189_, v_filter_3190_, v_view_x3f_3191_, v_toBind_3192_, v___f_3193_, v___f_3194_, v_a_3195_, v_x_3196_, v___y_3197_);
lean_dec(v_a_3195_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3202_, lean_object* v_n_3203_, lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_n_u2080_3210_, lean_object* v_filter_3211_, lean_object* v_view_x3f_3212_, lean_object* v_toBind_3213_, lean_object* v___f_3214_, lean_object* v___f_3215_, lean_object* v___x_3216_, lean_object* v_____do__lift_3217_){
_start:
{
if (lean_obj_tag(v_____do__lift_3217_) == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec_ref(v___x_3216_);
lean_dec(v___f_3215_);
lean_dec(v___f_3214_);
lean_dec(v_toBind_3213_);
lean_dec(v_view_x3f_3212_);
lean_dec(v_filter_3211_);
lean_dec(v_n_u2080_3210_);
lean_dec(v_inst_3209_);
lean_dec_ref(v_inst_3208_);
lean_dec(v_inst_3207_);
lean_dec_ref(v_inst_3206_);
lean_dec_ref(v_inst_3205_);
lean_dec_ref(v_inst_3204_);
lean_dec(v_n_3203_);
v___x_3218_ = lean_box(0);
v___x_3219_ = lean_apply_2(v_toPure_3202_, lean_box(0), v___x_3218_);
return v___x_3219_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3220_ = l_Lean_privateToUserName(v_n_3203_);
v___x_3221_ = l_Lean_Name_componentsRev(v___x_3220_);
v___x_3222_ = lean_box(0);
lean_inc(v_toPure_3202_);
v___f_3223_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3223_, 0, v_toPure_3202_);
lean_closure_set(v___f_3223_, 1, v___x_3222_);
lean_inc(v_toBind_3213_);
v___f_3224_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3224_, 0, v_toPure_3202_);
lean_closure_set(v___f_3224_, 1, v___x_3222_);
lean_closure_set(v___f_3224_, 2, v_inst_3204_);
lean_closure_set(v___f_3224_, 3, v_inst_3205_);
lean_closure_set(v___f_3224_, 4, v_inst_3206_);
lean_closure_set(v___f_3224_, 5, v_inst_3207_);
lean_closure_set(v___f_3224_, 6, v_inst_3208_);
lean_closure_set(v___f_3224_, 7, v_inst_3209_);
lean_closure_set(v___f_3224_, 8, v_n_u2080_3210_);
lean_closure_set(v___f_3224_, 9, v_filter_3211_);
lean_closure_set(v___f_3224_, 10, v_view_x3f_3212_);
lean_closure_set(v___f_3224_, 11, v_toBind_3213_);
lean_closure_set(v___f_3224_, 12, v___f_3214_);
lean_closure_set(v___f_3224_, 13, v___f_3215_);
v___x_3225_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3226_ = l_List_forIn_x27_loop___redArg(v___x_3216_, v___f_3224_, v___x_3221_, v___x_3225_);
lean_dec(v___x_3221_);
v___x_3227_ = lean_apply_4(v_toBind_3213_, lean_box(0), lean_box(0), v___x_3226_, v___f_3223_);
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3228_, lean_object* v_n_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_n_u2080_3236_, lean_object* v_filter_3237_, lean_object* v_view_x3f_3238_, lean_object* v_toBind_3239_, lean_object* v___f_3240_, lean_object* v___f_3241_, lean_object* v___x_3242_, lean_object* v_____do__lift_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3228_, v_n_3229_, v_inst_3230_, v_inst_3231_, v_inst_3232_, v_inst_3233_, v_inst_3234_, v_inst_3235_, v_n_u2080_3236_, v_filter_3237_, v_view_x3f_3238_, v_toBind_3239_, v___f_3240_, v___f_3241_, v___x_3242_, v_____do__lift_3243_);
lean_dec(v_____do__lift_3243_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_n_u2080_3251_, lean_object* v_filter_3252_, lean_object* v_view_x3f_3253_, lean_object* v_n_3254_){
_start:
{
lean_object* v___f_3255_; lean_object* v___f_3256_; lean_object* v___f_3257_; lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___y_3266_; uint8_t v___x_3274_; 
lean_inc_ref_n(v_inst_3245_, 7);
v___f_3255_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3255_, 0, v_inst_3245_);
v___f_3256_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3256_, 0, v_inst_3245_);
v___f_3257_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3257_, 0, v_inst_3245_);
v___f_3258_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3258_, 0, v_inst_3245_);
v___f_3259_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3259_, 0, v_inst_3245_);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___f_3255_);
lean_ctor_set(v___x_3260_, 1, v___f_3256_);
v___x_3261_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3261_, 0, lean_box(0));
lean_closure_set(v___x_3261_, 1, v_inst_3245_);
v___x_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
lean_ctor_set(v___x_3262_, 2, v___f_3257_);
lean_ctor_set(v___x_3262_, 3, v___f_3258_);
lean_ctor_set(v___x_3262_, 4, v___f_3259_);
v___x_3263_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3263_, 0, lean_box(0));
lean_closure_set(v___x_3263_, 1, v_inst_3245_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3274_ = l_Lean_Name_hasMacroScopes(v_n_3254_);
if (v___x_3274_ == 0)
{
lean_object* v_toApplicative_3275_; lean_object* v_toPure_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_toApplicative_3275_ = lean_ctor_get(v_inst_3245_, 0);
v_toPure_3276_ = lean_ctor_get(v_toApplicative_3275_, 1);
v___x_3277_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3276_);
v___x_3278_ = lean_apply_2(v_toPure_3276_, lean_box(0), v___x_3277_);
v___y_3266_ = v___x_3278_;
goto v___jp_3265_;
}
else
{
lean_object* v_toApplicative_3279_; lean_object* v_toPure_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_toApplicative_3279_ = lean_ctor_get(v_inst_3245_, 0);
v_toPure_3280_ = lean_ctor_get(v_toApplicative_3279_, 1);
v___x_3281_ = lean_box(0);
lean_inc(v_toPure_3280_);
v___x_3282_ = lean_apply_2(v_toPure_3280_, lean_box(0), v___x_3281_);
v___y_3266_ = v___x_3282_;
goto v___jp_3265_;
}
v___jp_3265_:
{
lean_object* v_toApplicative_3267_; lean_object* v_toBind_3268_; lean_object* v_toPure_3269_; lean_object* v___f_3270_; lean_object* v___f_3271_; lean_object* v___f_3272_; lean_object* v___x_3273_; 
v_toApplicative_3267_ = lean_ctor_get(v_inst_3245_, 0);
v_toBind_3268_ = lean_ctor_get(v_inst_3245_, 1);
lean_inc_n(v_toBind_3268_, 2);
v_toPure_3269_ = lean_ctor_get(v_toApplicative_3267_, 1);
lean_inc_n(v_toPure_3269_, 3);
v___f_3270_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3270_, 0, v_toPure_3269_);
v___f_3271_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3271_, 0, v_toPure_3269_);
v___f_3272_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3272_, 0, v_toPure_3269_);
lean_closure_set(v___f_3272_, 1, v_n_3254_);
lean_closure_set(v___f_3272_, 2, v_inst_3245_);
lean_closure_set(v___f_3272_, 3, v_inst_3246_);
lean_closure_set(v___f_3272_, 4, v_inst_3247_);
lean_closure_set(v___f_3272_, 5, v_inst_3248_);
lean_closure_set(v___f_3272_, 6, v_inst_3249_);
lean_closure_set(v___f_3272_, 7, v_inst_3250_);
lean_closure_set(v___f_3272_, 8, v_n_u2080_3251_);
lean_closure_set(v___f_3272_, 9, v_filter_3252_);
lean_closure_set(v___f_3272_, 10, v_view_x3f_3253_);
lean_closure_set(v___f_3272_, 11, v_toBind_3268_);
lean_closure_set(v___f_3272_, 12, v___f_3271_);
lean_closure_set(v___f_3272_, 13, v___f_3270_);
lean_closure_set(v___f_3272_, 14, v___x_3264_);
v___x_3273_ = lean_apply_4(v_toBind_3268_, lean_box(0), lean_box(0), v___y_3266_, v___f_3272_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_n_u2080_3290_, lean_object* v_filter_3291_, lean_object* v_view_x3f_3292_, lean_object* v_n_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3284_, v_inst_3285_, v_inst_3286_, v_inst_3287_, v_inst_3288_, v_inst_3289_, v_n_u2080_3290_, v_filter_3291_, v_view_x3f_3292_, v_n_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3295_, lean_object* v_x1_3296_, lean_object* v_x2_3297_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3298_ = l_Lean_Name_getPrefix(v_x2_3297_);
v___x_3299_ = l_Lean_Name_getPrefix(v_n_u2081_3295_);
v___x_3300_ = l_Lean_Name_isPrefixOf(v___x_3298_, v___x_3299_);
lean_dec(v___x_3299_);
lean_dec(v___x_3298_);
if (v___x_3300_ == 0)
{
lean_dec(v_x2_3297_);
return v_x1_3296_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_array_push(v_x1_3296_, v_x2_3297_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3302_, lean_object* v_x1_3303_, lean_object* v_x2_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3302_, v_x1_3303_, v_x2_3304_);
lean_dec(v_n_u2081_3302_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3306_, lean_object* v_n_u2081_3307_, lean_object* v_inst_3308_, lean_object* v_inst_3309_, lean_object* v_inst_3310_, lean_object* v_inst_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_n_u2080_3314_, lean_object* v_filter_3315_, lean_object* v_toPure_3316_, lean_object* v_____do__lift_3317_){
_start:
{
if (lean_obj_tag(v_____do__lift_3317_) == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
lean_dec(v_toPure_3316_);
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_view_3306_);
v___x_3319_ = l_Lean_rootNamespace;
v___x_3320_ = l_Lean_Name_append(v___x_3319_, v_n_u2081_3307_);
v___x_3321_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3308_, v_inst_3309_, v_inst_3310_, v_inst_3311_, v_inst_3312_, v_inst_3313_, v_n_u2080_3314_, v_filter_3315_, v___x_3318_, v___x_3320_);
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; 
lean_dec(v_filter_3315_);
lean_dec(v_n_u2080_3314_);
lean_dec(v_inst_3313_);
lean_dec_ref(v_inst_3312_);
lean_dec(v_inst_3311_);
lean_dec_ref(v_inst_3310_);
lean_dec_ref(v_inst_3309_);
lean_dec_ref(v_inst_3308_);
lean_dec(v_n_u2081_3307_);
lean_dec_ref(v_view_3306_);
v___x_3322_ = lean_apply_2(v_toPure_3316_, lean_box(0), v_____do__lift_3317_);
return v___x_3322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3323_, lean_object* v_inst_3324_, lean_object* v_inst_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_n_u2080_3330_, lean_object* v_filter_3331_, lean_object* v___x_3332_, lean_object* v_toBind_3333_, lean_object* v___f_3334_, uint8_t v_allowHorizAliases_3335_, lean_object* v___f_3336_, lean_object* v_____do__lift_3337_){
_start:
{
lean_object* v_aliases_3339_; 
if (lean_obj_tag(v_____do__lift_3337_) == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec_ref(v___f_3336_);
lean_dec(v___f_3334_);
lean_dec(v_toBind_3333_);
lean_dec_ref(v___x_3332_);
lean_dec(v_filter_3331_);
lean_dec(v_n_u2080_3330_);
lean_dec(v_inst_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec(v_inst_3327_);
lean_dec_ref(v_inst_3326_);
lean_dec_ref(v_inst_3325_);
lean_dec_ref(v_inst_3324_);
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_apply_2(v_toPure_3323_, lean_box(0), v___x_3345_);
return v___x_3346_;
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_dec(v_toPure_3323_);
v_val_3347_ = lean_ctor_get(v_____do__lift_3337_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v_____do__lift_3337_, 1);
lean_inc(v_n_u2080_3330_);
v___x_3348_ = l_Lean_getRevAliases(v_val_3347_, v_n_u2080_3330_);
v___x_3349_ = lean_array_mk(v___x_3348_);
if (v_allowHorizAliases_3335_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_array_get_size(v___x_3349_);
v___x_3352_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3353_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3354_ = lean_nat_dec_lt(v___x_3350_, v___x_3351_);
if (v___x_3354_ == 0)
{
lean_dec_ref(v___x_3349_);
lean_dec_ref(v___f_3336_);
v_aliases_3339_ = v___x_3352_;
goto v___jp_3338_;
}
else
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_nat_dec_le(v___x_3351_, v___x_3351_);
if (v___x_3355_ == 0)
{
if (v___x_3354_ == 0)
{
lean_dec_ref(v___x_3349_);
lean_dec_ref(v___f_3336_);
v_aliases_3339_ = v___x_3352_;
goto v___jp_3338_;
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3351_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3353_, v___f_3336_, v___x_3349_, v___x_3356_, v___x_3357_, v___x_3352_);
v_aliases_3339_ = v___x_3358_;
goto v___jp_3338_;
}
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3351_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3353_, v___f_3336_, v___x_3349_, v___x_3359_, v___x_3360_, v___x_3352_);
v_aliases_3339_ = v___x_3361_;
goto v___jp_3338_;
}
}
}
else
{
lean_dec_ref(v___f_3336_);
v_aliases_3339_ = v___x_3349_;
goto v___jp_3338_;
}
}
v___jp_3338_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3341_, 0, lean_box(0));
lean_closure_set(v___x_3341_, 1, v_inst_3324_);
lean_closure_set(v___x_3341_, 2, v_inst_3325_);
lean_closure_set(v___x_3341_, 3, v_inst_3326_);
lean_closure_set(v___x_3341_, 4, v_inst_3327_);
lean_closure_set(v___x_3341_, 5, v_inst_3328_);
lean_closure_set(v___x_3341_, 6, v_inst_3329_);
lean_closure_set(v___x_3341_, 7, v_n_u2080_3330_);
lean_closure_set(v___x_3341_, 8, v_filter_3331_);
lean_closure_set(v___x_3341_, 9, v___x_3340_);
v___x_3342_ = lean_unsigned_to_nat(0u);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3332_, v___x_3341_, v_aliases_3339_, v___x_3342_);
v___x_3344_ = lean_apply_4(v_toBind_3333_, lean_box(0), lean_box(0), v___x_3343_, v___f_3334_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_n_u2080_3369_, lean_object* v_filter_3370_, lean_object* v___x_3371_, lean_object* v_toBind_3372_, lean_object* v___f_3373_, lean_object* v_allowHorizAliases_3374_, lean_object* v___f_3375_, lean_object* v_____do__lift_3376_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3377_; lean_object* v_res_3378_; 
v_allowHorizAliases_boxed_3377_ = lean_unbox(v_allowHorizAliases_3374_);
v_res_3378_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3362_, v_inst_3363_, v_inst_3364_, v_inst_3365_, v_inst_3366_, v_inst_3367_, v_inst_3368_, v_n_u2080_3369_, v_filter_3370_, v___x_3371_, v_toBind_3372_, v___f_3373_, v_allowHorizAliases_boxed_3377_, v___f_3375_, v_____do__lift_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3379_, lean_object* v_____do__lift_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_____do__lift_3380_);
v___x_3382_ = lean_apply_2(v_toPure_3379_, lean_box(0), v___x_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_inst_3388_, lean_object* v_inst_3389_, lean_object* v_n_u2080_3390_, lean_object* v_filter_3391_, lean_object* v___x_3392_, lean_object* v_toPure_3393_, lean_object* v_____do__lift_3394_){
_start:
{
if (lean_obj_tag(v_____do__lift_3394_) == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec(v_toPure_3393_);
v___x_3395_ = l_Lean_rootNamespace;
v___x_3396_ = l_Lean_Name_append(v___x_3395_, v_n_u2081_3383_);
v___x_3397_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3384_, v_inst_3385_, v_inst_3386_, v_inst_3387_, v_inst_3388_, v_inst_3389_, v_n_u2080_3390_, v_filter_3391_, v___x_3392_, v___x_3396_);
return v___x_3397_;
}
else
{
lean_object* v___x_3398_; 
lean_dec(v___x_3392_);
lean_dec(v_filter_3391_);
lean_dec(v_n_u2080_3390_);
lean_dec(v_inst_3389_);
lean_dec_ref(v_inst_3388_);
lean_dec(v_inst_3387_);
lean_dec_ref(v_inst_3386_);
lean_dec_ref(v_inst_3385_);
lean_dec_ref(v_inst_3384_);
lean_dec(v_n_u2081_3383_);
v___x_3398_ = lean_apply_2(v_toPure_3393_, lean_box(0), v_____do__lift_3394_);
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3399_, lean_object* v_inst_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_n_u2080_3405_, uint8_t v_fullNames_3406_, uint8_t v_allowHorizAliases_3407_, lean_object* v_filter_3408_){
_start:
{
lean_object* v_view_3409_; lean_object* v_name_3410_; lean_object* v_n_u2081_3411_; lean_object* v___x_3412_; 
lean_inc(v_n_u2080_3405_);
v_view_3409_ = l_Lean_extractMacroScopes(v_n_u2080_3405_);
v_name_3410_ = lean_ctor_get(v_view_3409_, 0);
lean_inc(v_name_3410_);
v_n_u2081_3411_ = l_Lean_privateToUserName(v_name_3410_);
lean_inc_ref(v_inst_3399_);
v___x_3412_ = l_OptionT_instAlternative___redArg(v_inst_3399_);
if (v_fullNames_3406_ == 0)
{
lean_object* v_toApplicative_3413_; lean_object* v_getEnv_3414_; lean_object* v_toBind_3415_; lean_object* v_toPure_3416_; lean_object* v___f_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; lean_object* v___f_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_toApplicative_3413_ = lean_ctor_get(v_inst_3399_, 0);
v_getEnv_3414_ = lean_ctor_get(v_inst_3401_, 0);
lean_inc(v_getEnv_3414_);
v_toBind_3415_ = lean_ctor_get(v_inst_3399_, 1);
lean_inc_n(v_toBind_3415_, 3);
v_toPure_3416_ = lean_ctor_get(v_toApplicative_3413_, 1);
lean_inc_n(v_toPure_3416_, 3);
lean_inc(v_n_u2081_3411_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3417_, 0, v_n_u2081_3411_);
lean_inc(v_filter_3408_);
lean_inc(v_n_u2080_3405_);
lean_inc(v_inst_3404_);
lean_inc_ref(v_inst_3403_);
lean_inc(v_inst_3402_);
lean_inc_ref(v_inst_3401_);
lean_inc_ref(v_inst_3400_);
lean_inc_ref(v_inst_3399_);
v___f_3418_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3418_, 0, v_view_3409_);
lean_closure_set(v___f_3418_, 1, v_n_u2081_3411_);
lean_closure_set(v___f_3418_, 2, v_inst_3399_);
lean_closure_set(v___f_3418_, 3, v_inst_3400_);
lean_closure_set(v___f_3418_, 4, v_inst_3401_);
lean_closure_set(v___f_3418_, 5, v_inst_3402_);
lean_closure_set(v___f_3418_, 6, v_inst_3403_);
lean_closure_set(v___f_3418_, 7, v_inst_3404_);
lean_closure_set(v___f_3418_, 8, v_n_u2080_3405_);
lean_closure_set(v___f_3418_, 9, v_filter_3408_);
lean_closure_set(v___f_3418_, 10, v_toPure_3416_);
v___x_3419_ = lean_box(v_allowHorizAliases_3407_);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_3420_, 0, v_toPure_3416_);
lean_closure_set(v___f_3420_, 1, v_inst_3399_);
lean_closure_set(v___f_3420_, 2, v_inst_3400_);
lean_closure_set(v___f_3420_, 3, v_inst_3401_);
lean_closure_set(v___f_3420_, 4, v_inst_3402_);
lean_closure_set(v___f_3420_, 5, v_inst_3403_);
lean_closure_set(v___f_3420_, 6, v_inst_3404_);
lean_closure_set(v___f_3420_, 7, v_n_u2080_3405_);
lean_closure_set(v___f_3420_, 8, v_filter_3408_);
lean_closure_set(v___f_3420_, 9, v___x_3412_);
lean_closure_set(v___f_3420_, 10, v_toBind_3415_);
lean_closure_set(v___f_3420_, 11, v___f_3418_);
lean_closure_set(v___f_3420_, 12, v___x_3419_);
lean_closure_set(v___f_3420_, 13, v___f_3417_);
v___f_3421_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3421_, 0, v_toPure_3416_);
v___x_3422_ = lean_apply_4(v_toBind_3415_, lean_box(0), lean_box(0), v_getEnv_3414_, v___f_3421_);
v___x_3423_ = lean_apply_4(v_toBind_3415_, lean_box(0), lean_box(0), v___x_3422_, v___f_3420_);
return v___x_3423_;
}
else
{
lean_object* v_toApplicative_3424_; lean_object* v_toBind_3425_; lean_object* v_toPure_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; 
lean_dec_ref(v___x_3412_);
v_toApplicative_3424_ = lean_ctor_get(v_inst_3399_, 0);
v_toBind_3425_ = lean_ctor_get(v_inst_3399_, 1);
lean_inc(v_toBind_3425_);
v_toPure_3426_ = lean_ctor_get(v_toApplicative_3424_, 1);
lean_inc(v_toPure_3426_);
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_view_3409_);
lean_inc(v_n_u2081_3411_);
lean_inc_ref(v___x_3427_);
lean_inc(v_filter_3408_);
lean_inc(v_n_u2080_3405_);
lean_inc(v_inst_3404_);
lean_inc_ref(v_inst_3403_);
lean_inc(v_inst_3402_);
lean_inc_ref(v_inst_3401_);
lean_inc_ref(v_inst_3400_);
lean_inc_ref(v_inst_3399_);
v___x_3428_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3399_, v_inst_3400_, v_inst_3401_, v_inst_3402_, v_inst_3403_, v_inst_3404_, v_n_u2080_3405_, v_filter_3408_, v___x_3427_, v_n_u2081_3411_);
v___f_3429_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3429_, 0, v_n_u2081_3411_);
lean_closure_set(v___f_3429_, 1, v_inst_3399_);
lean_closure_set(v___f_3429_, 2, v_inst_3400_);
lean_closure_set(v___f_3429_, 3, v_inst_3401_);
lean_closure_set(v___f_3429_, 4, v_inst_3402_);
lean_closure_set(v___f_3429_, 5, v_inst_3403_);
lean_closure_set(v___f_3429_, 6, v_inst_3404_);
lean_closure_set(v___f_3429_, 7, v_n_u2080_3405_);
lean_closure_set(v___f_3429_, 8, v_filter_3408_);
lean_closure_set(v___f_3429_, 9, v___x_3427_);
lean_closure_set(v___f_3429_, 10, v_toPure_3426_);
v___x_3430_ = lean_apply_4(v_toBind_3425_, lean_box(0), lean_box(0), v___x_3428_, v___f_3429_);
return v___x_3430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_inst_3434_, lean_object* v_inst_3435_, lean_object* v_inst_3436_, lean_object* v_n_u2080_3437_, lean_object* v_fullNames_3438_, lean_object* v_allowHorizAliases_3439_, lean_object* v_filter_3440_){
_start:
{
uint8_t v_fullNames_boxed_3441_; uint8_t v_allowHorizAliases_boxed_3442_; lean_object* v_res_3443_; 
v_fullNames_boxed_3441_ = lean_unbox(v_fullNames_3438_);
v_allowHorizAliases_boxed_3442_ = lean_unbox(v_allowHorizAliases_3439_);
v_res_3443_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3431_, v_inst_3432_, v_inst_3433_, v_inst_3434_, v_inst_3435_, v_inst_3436_, v_n_u2080_3437_, v_fullNames_boxed_3441_, v_allowHorizAliases_boxed_3442_, v_filter_3440_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3444_, lean_object* v_inst_3445_, lean_object* v_inst_3446_, lean_object* v_inst_3447_, lean_object* v_inst_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_n_u2080_3451_, uint8_t v_fullNames_3452_, uint8_t v_allowHorizAliases_3453_, lean_object* v_filter_3454_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3445_, v_inst_3446_, v_inst_3447_, v_inst_3448_, v_inst_3449_, v_inst_3450_, v_n_u2080_3451_, v_fullNames_3452_, v_allowHorizAliases_3453_, v_filter_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3456_, lean_object* v_inst_3457_, lean_object* v_inst_3458_, lean_object* v_inst_3459_, lean_object* v_inst_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_n_u2080_3463_, lean_object* v_fullNames_3464_, lean_object* v_allowHorizAliases_3465_, lean_object* v_filter_3466_){
_start:
{
uint8_t v_fullNames_boxed_3467_; uint8_t v_allowHorizAliases_boxed_3468_; lean_object* v_res_3469_; 
v_fullNames_boxed_3467_ = lean_unbox(v_fullNames_3464_);
v_allowHorizAliases_boxed_3468_ = lean_unbox(v_allowHorizAliases_3465_);
v_res_3469_ = l_Lean_unresolveNameGlobal_x3f(v_m_3456_, v_inst_3457_, v_inst_3458_, v_inst_3459_, v_inst_3460_, v_inst_3461_, v_inst_3462_, v_n_u2080_3463_, v_fullNames_boxed_3467_, v_allowHorizAliases_boxed_3468_, v_filter_3466_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3470_, lean_object* v_n_u2080_3471_, lean_object* v_n_x3f_3472_){
_start:
{
if (lean_obj_tag(v_n_x3f_3472_) == 0)
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_apply_2(v_toPure_3470_, lean_box(0), v_n_u2080_3471_);
return v___x_3473_;
}
else
{
lean_object* v_val_3474_; lean_object* v___x_3475_; 
lean_dec(v_n_u2080_3471_);
v_val_3474_ = lean_ctor_get(v_n_x3f_3472_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v_n_x3f_3472_, 1);
v___x_3475_ = lean_apply_2(v_toPure_3470_, lean_box(0), v_val_3474_);
return v___x_3475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_n_u2080_3482_, uint8_t v_fullNames_3483_, uint8_t v_allowHorizAliases_3484_, lean_object* v_filter_3485_){
_start:
{
lean_object* v_toApplicative_3486_; lean_object* v_toBind_3487_; lean_object* v_toPure_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; 
v_toApplicative_3486_ = lean_ctor_get(v_inst_3476_, 0);
v_toBind_3487_ = lean_ctor_get(v_inst_3476_, 1);
lean_inc(v_toBind_3487_);
v_toPure_3488_ = lean_ctor_get(v_toApplicative_3486_, 1);
lean_inc(v_toPure_3488_);
lean_inc(v_n_u2080_3482_);
v___x_3489_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3476_, v_inst_3477_, v_inst_3478_, v_inst_3479_, v_inst_3480_, v_inst_3481_, v_n_u2080_3482_, v_fullNames_3483_, v_allowHorizAliases_3484_, v_filter_3485_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3490_, 0, v_toPure_3488_);
lean_closure_set(v___f_3490_, 1, v_n_u2080_3482_);
v___x_3491_ = lean_apply_4(v_toBind_3487_, lean_box(0), lean_box(0), v___x_3489_, v___f_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_n_u2080_3498_, lean_object* v_fullNames_3499_, lean_object* v_allowHorizAliases_3500_, lean_object* v_filter_3501_){
_start:
{
uint8_t v_fullNames_boxed_3502_; uint8_t v_allowHorizAliases_boxed_3503_; lean_object* v_res_3504_; 
v_fullNames_boxed_3502_ = lean_unbox(v_fullNames_3499_);
v_allowHorizAliases_boxed_3503_ = lean_unbox(v_allowHorizAliases_3500_);
v_res_3504_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3492_, v_inst_3493_, v_inst_3494_, v_inst_3495_, v_inst_3496_, v_inst_3497_, v_n_u2080_3498_, v_fullNames_boxed_3502_, v_allowHorizAliases_boxed_3503_, v_filter_3501_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3505_, lean_object* v_inst_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_n_u2080_3512_, uint8_t v_fullNames_3513_, uint8_t v_allowHorizAliases_3514_, lean_object* v_filter_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3506_, v_inst_3507_, v_inst_3508_, v_inst_3509_, v_inst_3510_, v_inst_3511_, v_n_u2080_3512_, v_fullNames_3513_, v_allowHorizAliases_3514_, v_filter_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3517_, lean_object* v_inst_3518_, lean_object* v_inst_3519_, lean_object* v_inst_3520_, lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_n_u2080_3524_, lean_object* v_fullNames_3525_, lean_object* v_allowHorizAliases_3526_, lean_object* v_filter_3527_){
_start:
{
uint8_t v_fullNames_boxed_3528_; uint8_t v_allowHorizAliases_boxed_3529_; lean_object* v_res_3530_; 
v_fullNames_boxed_3528_ = lean_unbox(v_fullNames_3525_);
v_allowHorizAliases_boxed_3529_ = lean_unbox(v_allowHorizAliases_3526_);
v_res_3530_ = l_Lean_unresolveNameGlobal(v_m_3517_, v_inst_3518_, v_inst_3519_, v_inst_3520_, v_inst_3521_, v_inst_3522_, v_inst_3523_, v_n_u2080_3524_, v_fullNames_boxed_3528_, v_allowHorizAliases_boxed_3529_, v_filter_3527_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3532_, lean_object* v_inst_3533_, lean_object* v_inst_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_n_3540_){
_start:
{
lean_object* v_map_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_map_3541_ = lean_ctor_get(v_toFunctor_3532_, 0);
lean_inc(v_map_3541_);
lean_dec_ref(v_toFunctor_3532_);
v___x_3542_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3543_ = l_Lean_resolveLocalName___redArg(v_inst_3533_, v_inst_3534_, v_inst_3535_, v_inst_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_n_3540_);
v___x_3544_ = lean_apply_4(v_map_3541_, lean_box(0), lean_box(0), v___x_3542_, v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_n_u2080_3552_, uint8_t v_fullNames_3553_){
_start:
{
lean_object* v_toApplicative_3554_; lean_object* v_toFunctor_3555_; uint8_t v___x_3556_; lean_object* v___f_3557_; lean_object* v___x_3558_; 
v_toApplicative_3554_ = lean_ctor_get(v_inst_3545_, 0);
v_toFunctor_3555_ = lean_ctor_get(v_toApplicative_3554_, 0);
v___x_3556_ = 0;
lean_inc(v_inst_3550_);
lean_inc_ref(v_inst_3549_);
lean_inc(v_inst_3548_);
lean_inc_ref(v_inst_3547_);
lean_inc_ref(v_inst_3546_);
lean_inc_ref(v_inst_3545_);
lean_inc_ref(v_toFunctor_3555_);
v___f_3557_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3557_, 0, v_toFunctor_3555_);
lean_closure_set(v___f_3557_, 1, v_inst_3545_);
lean_closure_set(v___f_3557_, 2, v_inst_3546_);
lean_closure_set(v___f_3557_, 3, v_inst_3547_);
lean_closure_set(v___f_3557_, 4, v_inst_3548_);
lean_closure_set(v___f_3557_, 5, v_inst_3549_);
lean_closure_set(v___f_3557_, 6, v_inst_3550_);
lean_closure_set(v___f_3557_, 7, v_inst_3551_);
v___x_3558_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3545_, v_inst_3546_, v_inst_3547_, v_inst_3548_, v_inst_3549_, v_inst_3550_, v_n_u2080_3552_, v_fullNames_3553_, v___x_3556_, v___f_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3559_, lean_object* v_inst_3560_, lean_object* v_inst_3561_, lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_n_u2080_3566_, lean_object* v_fullNames_3567_){
_start:
{
uint8_t v_fullNames_boxed_3568_; lean_object* v_res_3569_; 
v_fullNames_boxed_3568_ = lean_unbox(v_fullNames_3567_);
v_res_3569_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3559_, v_inst_3560_, v_inst_3561_, v_inst_3562_, v_inst_3563_, v_inst_3564_, v_inst_3565_, v_n_u2080_3566_, v_fullNames_boxed_3568_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_n_u2080_3578_, uint8_t v_fullNames_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3571_, v_inst_3572_, v_inst_3573_, v_inst_3574_, v_inst_3575_, v_inst_3576_, v_inst_3577_, v_n_u2080_3578_, v_fullNames_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_n_u2080_3589_, lean_object* v_fullNames_3590_){
_start:
{
uint8_t v_fullNames_boxed_3591_; lean_object* v_res_3592_; 
v_fullNames_boxed_3591_ = lean_unbox(v_fullNames_3590_);
v_res_3592_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3581_, v_inst_3582_, v_inst_3583_, v_inst_3584_, v_inst_3585_, v_inst_3586_, v_inst_3587_, v_inst_3588_, v_n_u2080_3589_, v_fullNames_boxed_3591_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_inst_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_n_u2080_3600_, uint8_t v_fullNames_3601_){
_start:
{
lean_object* v_toApplicative_3602_; lean_object* v_toBind_3603_; lean_object* v_toPure_3604_; lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; 
v_toApplicative_3602_ = lean_ctor_get(v_inst_3593_, 0);
v_toBind_3603_ = lean_ctor_get(v_inst_3593_, 1);
lean_inc(v_toBind_3603_);
v_toPure_3604_ = lean_ctor_get(v_toApplicative_3602_, 1);
lean_inc(v_toPure_3604_);
lean_inc(v_n_u2080_3600_);
v___x_3605_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3593_, v_inst_3594_, v_inst_3595_, v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_n_u2080_3600_, v_fullNames_3601_);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3606_, 0, v_toPure_3604_);
lean_closure_set(v___f_3606_, 1, v_n_u2080_3600_);
v___x_3607_ = lean_apply_4(v_toBind_3603_, lean_box(0), lean_box(0), v___x_3605_, v___f_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3608_, lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_n_u2080_3615_, lean_object* v_fullNames_3616_){
_start:
{
uint8_t v_fullNames_boxed_3617_; lean_object* v_res_3618_; 
v_fullNames_boxed_3617_ = lean_unbox(v_fullNames_3616_);
v_res_3618_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3608_, v_inst_3609_, v_inst_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_, v_inst_3614_, v_n_u2080_3615_, v_fullNames_boxed_3617_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3619_, lean_object* v_inst_3620_, lean_object* v_inst_3621_, lean_object* v_inst_3622_, lean_object* v_inst_3623_, lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_n_u2080_3627_, uint8_t v_fullNames_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3620_, v_inst_3621_, v_inst_3622_, v_inst_3623_, v_inst_3624_, v_inst_3625_, v_inst_3626_, v_n_u2080_3627_, v_fullNames_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_n_u2080_3638_, lean_object* v_fullNames_3639_){
_start:
{
uint8_t v_fullNames_boxed_3640_; lean_object* v_res_3641_; 
v_fullNames_boxed_3640_ = lean_unbox(v_fullNames_3639_);
v_res_3641_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3630_, v_inst_3631_, v_inst_3632_, v_inst_3633_, v_inst_3634_, v_inst_3635_, v_inst_3636_, v_inst_3637_, v_n_u2080_3638_, v_fullNames_boxed_3640_);
return v_res_3641_;
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
