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
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesRef;
static const lean_string_object l_Lean_registerReservedNamePredicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "failed to register reserved name suffix predicate, this operation can only be performed during initialization"};
static const lean_object* l_Lean_registerReservedNamePredicate___closed__0 = (const lean_object*)&l_Lean_registerReservedNamePredicate___closed__0_value;
static lean_once_cell_t l_Lean_registerReservedNamePredicate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerReservedNamePredicate___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "aliasExtension"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 78, 120, 122, 20, 252, 110, 252)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addAliasEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "privateInPublic"};
static const lean_object* l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 137, 140, 74, 72, 128, 49, 11)}};
static const lean_object* l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 227, .m_capacity = 227, .m_length = 226, .m_data = "(module system) Export `private` declarations, allowing for arbitrary access to them while code is being ported to the module system. Such accesses will generate warnings\n    unless `backward.privateInPublic.warn` is disabled."};
static const lean_object* l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ResolveName"};
static const lean_object* l_Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 161, 136, 183, 131, 203, 158, 84)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 154, 217, 244, 61, 155, 3, 144)}};
static const lean_object* l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_backward_privateInPublic;
static const lean_string_object l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 137, 140, 74, 72, 128, 49, 11)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 52, 68, 203, 224, 27, 156, 169)}};
static const lean_object* l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "(module system) Warn on accesses to `private` declarations that are allowed only by `backward.privateInPublic` being enabled."};
static const lean_object* l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 161, 136, 183, 131, 203, 158, 84)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 154, 217, 244, 61, 155, 3, 144)}};
static const lean_ctor_object l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(50, 1, 203, 3, 164, 240, 100, 244)}};
static const lean_object* l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_));
v___x_66_ = lean_st_mk_ref(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object* v___x_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_st_ref_get(v___x_104_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v___x_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(v___x_108_);
lean_dec(v___x_108_);
return v_res_110_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = l_Lean_reservedNamePredicatesRef;
v___f_112_ = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___f_114_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_box(2);
v___x_117_ = l_Lean_registerEnvExtension___redArg(v___f_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
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
lean_inc(v_asyncMode_147_);
v___x_148_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_149_ = lean_box(0);
lean_inc_ref(v_env_144_);
v___x_150_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_148_, v___x_146_, v_env_144_, v_asyncMode_147_, v___x_149_);
lean_dec(v_asyncMode_147_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; 
v___x_198_ = ((size_t)5ULL);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_shift_left(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; 
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_203_ = lean_usize_sub(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_205_, size_t v_x_206_, size_t v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v_es_210_; size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; size_t v___x_214_; lean_object* v_j_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_es_210_ = lean_ctor_get(v_x_205_, 0);
v___x_211_ = ((size_t)5ULL);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1);
v___x_214_ = lean_usize_land(v_x_206_, v___x_213_);
v_j_215_ = lean_usize_to_nat(v___x_214_);
v___x_216_ = lean_array_get_size(v_es_210_);
v___x_217_ = lean_nat_dec_lt(v_j_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_j_215_);
lean_dec(v_x_209_);
lean_dec(v_x_208_);
return v_x_205_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_254_; 
lean_inc_ref(v_es_210_);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v_x_205_, 0);
lean_dec(v_unused_255_);
v___x_219_ = v_x_205_;
v_isShared_220_ = v_isSharedCheck_254_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_x_205_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_254_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_v_221_; lean_object* v___x_222_; lean_object* v_xs_x27_223_; lean_object* v___y_225_; 
v_v_221_ = lean_array_fget(v_es_210_, v_j_215_);
v___x_222_ = lean_box(0);
v_xs_x27_223_ = lean_array_fset(v_es_210_, v_j_215_, v___x_222_);
switch(lean_obj_tag(v_v_221_))
{
case 0:
{
lean_object* v_key_230_; lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_key_230_ = lean_ctor_get(v_v_221_, 0);
v_val_231_ = lean_ctor_get(v_v_221_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v_v_221_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_inc(v_key_230_);
lean_dec(v_v_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; 
v___x_235_ = lean_name_eq(v_x_208_, v_key_230_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_233_);
v___x_236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_230_, v_val_231_, v_x_208_, v_x_209_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___y_225_ = v___x_237_;
goto v___jp_224_;
}
else
{
lean_object* v___x_239_; 
lean_dec(v_val_231_);
lean_dec(v_key_230_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_x_209_);
lean_ctor_set(v___x_233_, 0, v_x_208_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_x_208_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_x_209_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
}
}
}
case 1:
{
lean_object* v_node_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
v_node_242_ = lean_ctor_get(v_v_221_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_v_221_);
if (v_isSharedCheck_252_ == 0)
{
v___x_244_ = v_v_221_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_node_242_);
lean_dec(v_v_221_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
size_t v___x_246_; size_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_246_ = lean_usize_shift_right(v_x_206_, v___x_211_);
v___x_247_ = lean_usize_add(v_x_207_, v___x_212_);
v___x_248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_242_, v___x_246_, v___x_247_, v_x_208_, v_x_209_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_248_);
v___x_250_ = v___x_244_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v___y_225_ = v___x_250_;
goto v___jp_224_;
}
}
}
default: 
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_x_208_);
lean_ctor_set(v___x_253_, 1, v_x_209_);
v___y_225_ = v___x_253_;
goto v___jp_224_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_array_fset(v_xs_x27_223_, v_j_215_, v___y_225_);
lean_dec(v_j_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_226_);
v___x_228_ = v___x_219_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
else
{
lean_object* v_ks_256_; lean_object* v_vs_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_277_; 
v_ks_256_ = lean_ctor_get(v_x_205_, 0);
v_vs_257_ = lean_ctor_get(v_x_205_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_277_ == 0)
{
v___x_259_ = v_x_205_;
v_isShared_260_ = v_isSharedCheck_277_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_vs_257_);
lean_inc(v_ks_256_);
lean_dec(v_x_205_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_277_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_ks_256_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_vs_257_);
v___x_262_ = v_reuseFailAlloc_276_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v_newNode_263_; uint8_t v___y_265_; size_t v___x_271_; uint8_t v___x_272_; 
v_newNode_263_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_262_, v_x_208_, v_x_209_);
v___x_271_ = ((size_t)7ULL);
v___x_272_ = lean_usize_dec_le(v___x_271_, v_x_207_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_263_);
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_nat_dec_lt(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
v___y_265_ = v___x_275_;
goto v___jp_264_;
}
else
{
v___y_265_ = v___x_272_;
goto v___jp_264_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
lean_object* v_ks_266_; lean_object* v_vs_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_ks_266_ = lean_ctor_get(v_newNode_263_, 0);
lean_inc_ref(v_ks_266_);
v_vs_267_ = lean_ctor_get(v_newNode_263_, 1);
lean_inc_ref(v_vs_267_);
lean_dec_ref(v_newNode_263_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2);
v___x_270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_207_, v_ks_266_, v_vs_267_, v___x_268_, v___x_269_);
lean_dec_ref(v_vs_267_);
lean_dec_ref(v_ks_266_);
return v___x_270_;
}
else
{
return v_newNode_263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_278_, lean_object* v_keys_279_, lean_object* v_vals_280_, lean_object* v_i_281_, lean_object* v_entries_282_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_array_get_size(v_keys_279_);
v___x_284_ = lean_nat_dec_lt(v_i_281_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec(v_i_281_);
return v_entries_282_;
}
else
{
lean_object* v_k_285_; lean_object* v_v_286_; uint64_t v___y_288_; 
v_k_285_ = lean_array_fget_borrowed(v_keys_279_, v_i_281_);
v_v_286_ = lean_array_fget_borrowed(v_vals_280_, v_i_281_);
if (lean_obj_tag(v_k_285_) == 0)
{
uint64_t v___x_299_; 
v___x_299_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_288_ = v___x_299_;
goto v___jp_287_;
}
else
{
uint64_t v_hash_300_; 
v_hash_300_ = lean_ctor_get_uint64(v_k_285_, sizeof(void*)*2);
v___y_288_ = v_hash_300_;
goto v___jp_287_;
}
v___jp_287_:
{
size_t v_h_289_; size_t v___x_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v_h_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_h_289_ = lean_uint64_to_usize(v___y_288_);
v___x_290_ = ((size_t)5ULL);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_sub(v_depth_278_, v___x_292_);
v___x_294_ = lean_usize_mul(v___x_290_, v___x_293_);
v_h_295_ = lean_usize_shift_right(v_h_289_, v___x_294_);
v___x_296_ = lean_nat_add(v_i_281_, v___x_291_);
lean_dec(v_i_281_);
lean_inc(v_v_286_);
lean_inc(v_k_285_);
v___x_297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_282_, v_h_295_, v_depth_278_, v_k_285_, v_v_286_);
v_i_281_ = v___x_296_;
v_entries_282_ = v___x_297_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_301_, lean_object* v_keys_302_, lean_object* v_vals_303_, lean_object* v_i_304_, lean_object* v_entries_305_){
_start:
{
size_t v_depth_boxed_306_; lean_object* v_res_307_; 
v_depth_boxed_306_ = lean_unbox_usize(v_depth_301_);
lean_dec(v_depth_301_);
v_res_307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_306_, v_keys_302_, v_vals_303_, v_i_304_, v_entries_305_);
lean_dec_ref(v_vals_303_);
lean_dec_ref(v_keys_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
size_t v_x_1112__boxed_313_; size_t v_x_1113__boxed_314_; lean_object* v_res_315_; 
v_x_1112__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_x_1113__boxed_314_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_res_315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_308_, v_x_1112__boxed_313_, v_x_1113__boxed_314_, v_x_311_, v_x_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint64_t v___y_320_; 
if (lean_obj_tag(v_x_317_) == 0)
{
uint64_t v___x_324_; 
v___x_324_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_320_ = v___x_324_;
goto v___jp_319_;
}
else
{
uint64_t v_hash_325_; 
v_hash_325_ = lean_ctor_get_uint64(v_x_317_, sizeof(void*)*2);
v___y_320_ = v_hash_325_;
goto v___jp_319_;
}
v___jp_319_:
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_uint64_to_usize(v___y_320_);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_316_, v___x_321_, v___x_322_, v_x_317_, v_x_318_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
return v_x_326_;
}
else
{
lean_object* v_key_328_; lean_object* v_value_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_356_; 
v_key_328_ = lean_ctor_get(v_x_327_, 0);
v_value_329_ = lean_ctor_get(v_x_327_, 1);
v_tail_330_ = lean_ctor_get(v_x_327_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_356_ == 0)
{
v___x_332_ = v_x_327_;
v_isShared_333_ = v_isSharedCheck_356_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_value_329_);
lean_inc(v_key_328_);
lean_dec(v_x_327_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_356_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint64_t v___y_336_; 
v___x_334_ = lean_array_get_size(v_x_326_);
if (lean_obj_tag(v_key_328_) == 0)
{
uint64_t v___x_354_; 
v___x_354_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_336_ = v___x_354_;
goto v___jp_335_;
}
else
{
uint64_t v_hash_355_; 
v_hash_355_ = lean_ctor_get_uint64(v_key_328_, sizeof(void*)*2);
v___y_336_ = v_hash_355_;
goto v___jp_335_;
}
v___jp_335_:
{
uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___y_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___y_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_334_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v___x_348_ = lean_array_uget_borrowed(v_x_326_, v___x_347_);
lean_inc(v___x_348_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 2, v___x_348_);
v___x_350_ = v___x_332_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_key_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_value_329_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v___x_348_);
v___x_350_ = v_reuseFailAlloc_353_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_array_uset(v_x_326_, v___x_347_, v___x_350_);
v_x_326_ = v___x_351_;
v_x_327_ = v_tail_330_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_357_, lean_object* v_source_358_, lean_object* v_target_359_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_array_get_size(v_source_358_);
v___x_361_ = lean_nat_dec_lt(v_i_357_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec_ref(v_source_358_);
lean_dec(v_i_357_);
return v_target_359_;
}
else
{
lean_object* v_es_362_; lean_object* v___x_363_; lean_object* v_source_364_; lean_object* v_target_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_es_362_ = lean_array_fget(v_source_358_, v_i_357_);
v___x_363_ = lean_box(0);
v_source_364_ = lean_array_fset(v_source_358_, v_i_357_, v___x_363_);
v_target_365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_359_, v_es_362_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_i_357_, v___x_366_);
lean_dec(v_i_357_);
v_i_357_ = v___x_367_;
v_source_358_ = v_source_364_;
v_target_359_ = v_target_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_nbuckets_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = lean_array_get_size(v_data_369_);
v___x_371_ = lean_unsigned_to_nat(2u);
v_nbuckets_372_ = lean_nat_mul(v___x_370_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_box(0);
v___x_375_ = lean_mk_array(v_nbuckets_372_, v___x_374_);
v___x_376_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_373_, v_data_369_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
uint8_t v___x_379_; 
v___x_379_ = 0;
return v___x_379_;
}
else
{
lean_object* v_key_380_; lean_object* v_tail_381_; uint8_t v___x_382_; 
v_key_380_ = lean_ctor_get(v_x_378_, 0);
v_tail_381_ = lean_ctor_get(v_x_378_, 2);
v___x_382_ = lean_name_eq(v_key_380_, v_a_377_);
if (v___x_382_ == 0)
{
v_x_378_ = v_tail_381_;
goto _start;
}
else
{
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_384_, v_x_385_);
lean_dec(v_x_385_);
lean_dec(v_a_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_388_, lean_object* v_b_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_dec(v_b_389_);
lean_dec(v_a_388_);
return v_x_390_;
}
else
{
lean_object* v_key_391_; lean_object* v_value_392_; lean_object* v_tail_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
v_key_391_ = lean_ctor_get(v_x_390_, 0);
v_value_392_ = lean_ctor_get(v_x_390_, 1);
v_tail_393_ = lean_ctor_get(v_x_390_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_405_ == 0)
{
v___x_395_ = v_x_390_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_tail_393_);
lean_inc(v_value_392_);
lean_inc(v_key_391_);
lean_dec(v_x_390_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; 
v___x_397_ = lean_name_eq(v_key_391_, v_a_388_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_388_, v_b_389_, v_tail_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 2, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_key_391_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_value_392_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v___x_403_; 
lean_dec(v_value_392_);
lean_dec(v_key_391_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v_b_389_);
lean_ctor_set(v___x_395_, 0, v_a_388_);
v___x_403_ = v___x_395_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_388_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_b_389_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_tail_393_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_406_, lean_object* v_a_407_, lean_object* v_b_408_){
_start:
{
lean_object* v_size_409_; lean_object* v_buckets_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_456_; 
v_size_409_ = lean_ctor_get(v_m_406_, 0);
v_buckets_410_ = lean_ctor_get(v_m_406_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_m_406_);
if (v_isSharedCheck_456_ == 0)
{
v___x_412_ = v_m_406_;
v_isShared_413_ = v_isSharedCheck_456_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_buckets_410_);
lean_inc(v_size_409_);
lean_dec(v_m_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_456_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint64_t v___y_416_; 
v___x_414_ = lean_array_get_size(v_buckets_410_);
if (lean_obj_tag(v_a_407_) == 0)
{
uint64_t v___x_454_; 
v___x_454_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_416_ = v___x_454_;
goto v___jp_415_;
}
else
{
uint64_t v_hash_455_; 
v_hash_455_ = lean_ctor_get_uint64(v_a_407_, sizeof(void*)*2);
v___y_416_ = v_hash_455_;
goto v___jp_415_;
}
v___jp_415_:
{
uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v_fold_419_; uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; lean_object* v_bkt_428_; uint8_t v___x_429_; 
v___x_417_ = 32ULL;
v___x_418_ = lean_uint64_shift_right(v___y_416_, v___x_417_);
v_fold_419_ = lean_uint64_xor(v___y_416_, v___x_418_);
v___x_420_ = 16ULL;
v___x_421_ = lean_uint64_shift_right(v_fold_419_, v___x_420_);
v___x_422_ = lean_uint64_xor(v_fold_419_, v___x_421_);
v___x_423_ = lean_uint64_to_usize(v___x_422_);
v___x_424_ = lean_usize_of_nat(v___x_414_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_sub(v___x_424_, v___x_425_);
v___x_427_ = lean_usize_land(v___x_423_, v___x_426_);
v_bkt_428_ = lean_array_uget_borrowed(v_buckets_410_, v___x_427_);
v___x_429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_407_, v_bkt_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v_size_x27_431_; lean_object* v___x_432_; lean_object* v_buckets_x27_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v_size_x27_431_ = lean_nat_add(v_size_409_, v___x_430_);
lean_dec(v_size_409_);
lean_inc(v_bkt_428_);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v_a_407_);
lean_ctor_set(v___x_432_, 1, v_b_408_);
lean_ctor_set(v___x_432_, 2, v_bkt_428_);
v_buckets_x27_433_ = lean_array_uset(v_buckets_410_, v___x_427_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = lean_nat_mul(v_size_x27_431_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(3u);
v___x_437_ = lean_nat_div(v___x_435_, v___x_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_array_get_size(v_buckets_x27_433_);
v___x_439_ = lean_nat_dec_le(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
if (v___x_439_ == 0)
{
lean_object* v_val_440_; lean_object* v___x_442_; 
v_val_440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_433_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_val_440_);
lean_ctor_set(v___x_412_, 0, v_size_x27_431_);
v___x_442_ = v___x_412_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_size_x27_431_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_val_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_445_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_buckets_x27_433_);
lean_ctor_set(v___x_412_, 0, v_size_x27_431_);
v___x_445_ = v___x_412_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_size_x27_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_buckets_x27_433_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v___x_447_; lean_object* v_buckets_x27_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
lean_inc(v_bkt_428_);
v___x_447_ = lean_box(0);
v_buckets_x27_448_ = lean_array_uset(v_buckets_410_, v___x_427_, v___x_447_);
v___x_449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_407_, v_b_408_, v_bkt_428_);
v___x_450_ = lean_array_uset(v_buckets_x27_448_, v___x_427_, v___x_449_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_450_);
v___x_452_ = v___x_412_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_size_409_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
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
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
uint8_t v_stage_u2081_460_; 
v_stage_u2081_460_ = lean_ctor_get_uint8(v_x_457_, sizeof(void*)*2);
if (v_stage_u2081_460_ == 0)
{
lean_object* v_map_u2081_461_; lean_object* v_map_u2082_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_map_u2081_461_ = lean_ctor_get(v_x_457_, 0);
v_map_u2082_462_ = lean_ctor_get(v_x_457_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_457_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v_x_457_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_map_u2082_462_);
lean_inc(v_map_u2081_461_);
lean_dec(v_x_457_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_462_, v_x_458_, v_x_459_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_map_u2081_461_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, sizeof(void*)*2, v_stage_u2081_460_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_map_u2081_471_; lean_object* v_map_u2082_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
v_map_u2081_471_ = lean_ctor_get(v_x_457_, 0);
v_map_u2082_472_ = lean_ctor_get(v_x_457_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_457_);
if (v_isSharedCheck_480_ == 0)
{
v___x_474_ = v_x_457_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_map_u2082_472_);
lean_inc(v_map_u2081_471_);
lean_dec(v_x_457_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_471_, v_x_458_, v_x_459_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_map_u2082_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_479_, sizeof(void*)*2, v_stage_u2081_460_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v___x_483_; 
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v_key_484_; lean_object* v_value_485_; lean_object* v_tail_486_; uint8_t v___x_487_; 
v_key_484_ = lean_ctor_get(v_x_482_, 0);
v_value_485_ = lean_ctor_get(v_x_482_, 1);
v_tail_486_ = lean_ctor_get(v_x_482_, 2);
v___x_487_ = lean_name_eq(v_key_484_, v_a_481_);
if (v___x_487_ == 0)
{
v_x_482_ = v_tail_486_;
goto _start;
}
else
{
lean_object* v___x_489_; 
lean_inc(v_value_485_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_value_485_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_490_, lean_object* v_x_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_490_, v_x_491_);
lean_dec(v_x_491_);
lean_dec(v_a_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_buckets_495_; lean_object* v___x_496_; uint64_t v___y_498_; 
v_buckets_495_ = lean_ctor_get(v_m_493_, 1);
v___x_496_ = lean_array_get_size(v_buckets_495_);
if (lean_obj_tag(v_a_494_) == 0)
{
uint64_t v___x_512_; 
v___x_512_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_498_ = v___x_512_;
goto v___jp_497_;
}
else
{
uint64_t v_hash_513_; 
v_hash_513_ = lean_ctor_get_uint64(v_a_494_, sizeof(void*)*2);
v___y_498_ = v_hash_513_;
goto v___jp_497_;
}
v___jp_497_:
{
uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v_fold_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_499_ = 32ULL;
v___x_500_ = lean_uint64_shift_right(v___y_498_, v___x_499_);
v_fold_501_ = lean_uint64_xor(v___y_498_, v___x_500_);
v___x_502_ = 16ULL;
v___x_503_ = lean_uint64_shift_right(v_fold_501_, v___x_502_);
v___x_504_ = lean_uint64_xor(v_fold_501_, v___x_503_);
v___x_505_ = lean_uint64_to_usize(v___x_504_);
v___x_506_ = lean_usize_of_nat(v___x_496_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_usize_land(v___x_505_, v___x_508_);
v___x_510_ = lean_array_uget_borrowed(v_buckets_495_, v___x_509_);
v___x_511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_494_, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_m_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_517_, lean_object* v_vals_518_, lean_object* v_i_519_, lean_object* v_k_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_keys_517_);
v___x_522_ = lean_nat_dec_lt(v_i_519_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_i_519_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_k_x27_524_; uint8_t v___x_525_; 
v_k_x27_524_ = lean_array_fget_borrowed(v_keys_517_, v_i_519_);
v___x_525_ = lean_name_eq(v_k_520_, v_k_x27_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_i_519_, v___x_526_);
lean_dec(v_i_519_);
v_i_519_ = v___x_527_;
goto _start;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_array_fget_borrowed(v_vals_518_, v_i_519_);
lean_dec(v_i_519_);
lean_inc(v___x_529_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_531_, lean_object* v_vals_532_, lean_object* v_i_533_, lean_object* v_k_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_531_, v_vals_532_, v_i_533_, v_k_534_);
lean_dec(v_k_534_);
lean_dec_ref(v_vals_532_);
lean_dec_ref(v_keys_531_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_536_, size_t v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_es_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_560_; 
v_es_539_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_560_ == 0)
{
v___x_541_ = v_x_536_;
v_isShared_542_ = v_isSharedCheck_560_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_es_539_);
lean_dec(v_x_536_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_560_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v_j_547_; lean_object* v___x_548_; 
v___x_543_ = lean_box(2);
v___x_544_ = ((size_t)5ULL);
v___x_545_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1);
v___x_546_ = lean_usize_land(v_x_537_, v___x_545_);
v_j_547_ = lean_usize_to_nat(v___x_546_);
v___x_548_ = lean_array_get(v___x_543_, v_es_539_, v_j_547_);
lean_dec(v_j_547_);
lean_dec_ref(v_es_539_);
switch(lean_obj_tag(v___x_548_))
{
case 0:
{
lean_object* v_key_549_; lean_object* v_val_550_; uint8_t v___x_551_; 
v_key_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_key_549_);
v_val_550_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_val_550_);
lean_dec_ref(v___x_548_);
v___x_551_ = lean_name_eq(v_x_538_, v_key_549_);
lean_dec(v_key_549_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec(v_val_550_);
lean_del_object(v___x_541_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
else
{
lean_object* v___x_554_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 0, v_val_550_);
v___x_554_ = v___x_541_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_val_550_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
case 1:
{
lean_object* v_node_556_; size_t v___x_557_; 
lean_del_object(v___x_541_);
v_node_556_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_node_556_);
lean_dec_ref(v___x_548_);
v___x_557_ = lean_usize_shift_right(v_x_537_, v___x_544_);
v_x_536_ = v_node_556_;
v_x_537_ = v___x_557_;
goto _start;
}
default: 
{
lean_object* v___x_559_; 
lean_del_object(v___x_541_);
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
}
}
else
{
lean_object* v_ks_561_; lean_object* v_vs_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_ks_561_ = lean_ctor_get(v_x_536_, 0);
lean_inc_ref(v_ks_561_);
v_vs_562_ = lean_ctor_get(v_x_536_, 1);
lean_inc_ref(v_vs_562_);
lean_dec_ref(v_x_536_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_561_, v_vs_562_, v___x_563_, v_x_538_);
lean_dec_ref(v_vs_562_);
lean_dec_ref(v_ks_561_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
size_t v_x_1644__boxed_568_; lean_object* v_res_569_; 
v_x_1644__boxed_568_ = lean_unbox_usize(v_x_566_);
lean_dec(v_x_566_);
v_res_569_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_565_, v_x_1644__boxed_568_, v_x_567_);
lean_dec(v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
uint64_t v___y_573_; 
if (lean_obj_tag(v_x_571_) == 0)
{
uint64_t v___x_576_; 
v___x_576_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_573_ = v___x_576_;
goto v___jp_572_;
}
else
{
uint64_t v_hash_577_; 
v_hash_577_ = lean_ctor_get_uint64(v_x_571_, sizeof(void*)*2);
v___y_573_ = v_hash_577_;
goto v___jp_572_;
}
v___jp_572_:
{
size_t v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_uint64_to_usize(v___y_573_);
v___x_575_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_570_, v___x_574_, v_x_571_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_578_, v_x_579_);
lean_dec(v_x_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_stage_u2081_583_; 
v_stage_u2081_583_ = lean_ctor_get_uint8(v_x_581_, sizeof(void*)*2);
if (v_stage_u2081_583_ == 0)
{
lean_object* v_map_u2081_584_; lean_object* v_map_u2082_585_; lean_object* v___x_586_; 
v_map_u2081_584_ = lean_ctor_get(v_x_581_, 0);
lean_inc_ref(v_map_u2081_584_);
v_map_u2082_585_ = lean_ctor_get(v_x_581_, 1);
lean_inc_ref(v_map_u2082_585_);
lean_dec_ref(v_x_581_);
v___x_586_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_585_, v_x_582_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_584_, v_x_582_);
lean_dec_ref(v_map_u2081_584_);
return v___x_587_;
}
else
{
lean_dec_ref(v_map_u2081_584_);
return v___x_586_;
}
}
else
{
lean_object* v_map_u2081_588_; lean_object* v___x_589_; 
v_map_u2081_588_ = lean_ctor_get(v_x_581_, 0);
lean_inc_ref(v_map_u2081_588_);
lean_dec_ref(v_x_581_);
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_588_, v_x_582_);
lean_dec_ref(v_map_u2081_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_590_, v_x_591_);
lean_dec(v_x_591_);
return v_res_592_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
uint8_t v___x_595_; 
v___x_595_ = 0;
return v___x_595_;
}
else
{
lean_object* v_head_596_; lean_object* v_tail_597_; uint8_t v___x_598_; 
v_head_596_ = lean_ctor_get(v_x_594_, 0);
v_tail_597_ = lean_ctor_get(v_x_594_, 1);
v___x_598_ = lean_name_eq(v_a_593_, v_head_596_);
if (v___x_598_ == 0)
{
v_x_594_ = v_tail_597_;
goto _start;
}
else
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_600_, lean_object* v_x_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_600_, v_x_601_);
lean_dec(v_x_601_);
lean_dec(v_a_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_604_, lean_object* v_e_605_){
_start:
{
lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_623_; 
v_fst_606_ = lean_ctor_get(v_e_605_, 0);
v_snd_607_ = lean_ctor_get(v_e_605_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_e_605_);
if (v_isSharedCheck_623_ == 0)
{
v___x_609_ = v_e_605_;
v_isShared_610_ = v_isSharedCheck_623_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
lean_dec(v_e_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_623_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; 
lean_inc_ref(v_s_604_);
v___x_611_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_604_, v_fst_606_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_box(0);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 1);
lean_ctor_set(v___x_609_, 1, v___x_612_);
lean_ctor_set(v___x_609_, 0, v_snd_607_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_snd_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_604_, v_fst_606_, v___x_614_);
return v___x_615_;
}
}
else
{
lean_object* v_val_617_; uint8_t v___x_618_; 
v_val_617_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_617_);
lean_dec_ref(v___x_611_);
v___x_618_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_607_, v_val_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_620_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 1);
lean_ctor_set(v___x_609_, 1, v_val_617_);
lean_ctor_set(v___x_609_, 0, v_snd_607_);
v___x_620_ = v___x_609_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_snd_607_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_val_617_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_604_, v_fst_606_, v___x_620_);
return v___x_621_;
}
}
else
{
lean_dec(v_val_617_);
lean_del_object(v___x_609_);
lean_dec(v_snd_607_);
lean_dec(v_fst_606_);
return v_s_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_628_, v_x_629_, v_x_630_);
lean_dec(v_x_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_638_, v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_641_, v_x_642_, v_x_643_);
lean_dec(v_x_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_646_, v_a_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_649_, lean_object* v_m_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_649_, v_m_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_m_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_654_, v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_658_, lean_object* v_m_659_, lean_object* v_a_660_, lean_object* v_b_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_659_, v_a_660_, v_b_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, size_t v_x_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_664_, v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
size_t v_x_1826__boxed_672_; lean_object* v_res_673_; 
v_x_1826__boxed_672_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_res_673_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_668_, v_x_669_, v_x_1826__boxed_672_, v_x_671_);
lean_dec(v_x_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_678_, lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_678_, v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_682_, lean_object* v_x_683_, size_t v_x_684_, size_t v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_683_, v_x_684_, v_x_685_, v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
size_t v_x_1842__boxed_695_; size_t v_x_1843__boxed_696_; lean_object* v_res_697_; 
v_x_1842__boxed_695_ = lean_unbox_usize(v_x_691_);
lean_dec(v_x_691_);
v_x_1843__boxed_696_ = lean_unbox_usize(v_x_692_);
lean_dec(v_x_692_);
v_res_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_689_, v_x_690_, v_x_1842__boxed_695_, v_x_1843__boxed_696_, v_x_693_, v_x_694_);
return v_res_697_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_698_, lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
uint8_t v___x_701_; 
v___x_701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_699_, v_x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_702_, lean_object* v_a_703_, lean_object* v_x_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_702_, v_a_703_, v_x_704_);
lean_dec(v_x_704_);
lean_dec(v_a_703_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_707_, lean_object* v_data_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_710_, lean_object* v_a_711_, lean_object* v_b_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_711_, v_b_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_715_, lean_object* v_keys_716_, lean_object* v_vals_717_, lean_object* v_heq_718_, lean_object* v_i_719_, lean_object* v_k_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_716_, v_vals_717_, v_i_719_, v_k_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_722_, lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_heq_725_, lean_object* v_i_726_, lean_object* v_k_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_722_, v_keys_723_, v_vals_724_, v_heq_725_, v_i_726_, v_k_727_);
lean_dec(v_k_727_);
lean_dec_ref(v_vals_724_);
lean_dec_ref(v_keys_723_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_729_, lean_object* v_n_730_, lean_object* v_k_731_, lean_object* v_v_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_730_, v_k_731_, v_v_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_734_, size_t v_depth_735_, lean_object* v_keys_736_, lean_object* v_vals_737_, lean_object* v_heq_738_, lean_object* v_i_739_, lean_object* v_entries_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_735_, v_keys_736_, v_vals_737_, v_i_739_, v_entries_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_742_, lean_object* v_depth_743_, lean_object* v_keys_744_, lean_object* v_vals_745_, lean_object* v_heq_746_, lean_object* v_i_747_, lean_object* v_entries_748_){
_start:
{
size_t v_depth_boxed_749_; lean_object* v_res_750_; 
v_depth_boxed_749_ = lean_unbox_usize(v_depth_743_);
lean_dec(v_depth_743_);
v_res_750_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_742_, v_depth_boxed_749_, v_keys_744_, v_vals_745_, v_heq_746_, v_i_747_, v_entries_748_);
lean_dec_ref(v_vals_745_);
lean_dec_ref(v_keys_744_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_751_, lean_object* v_i_752_, lean_object* v_source_753_, lean_object* v_target_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_752_, v_source_753_, v_target_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_757_, v_x_758_, v_x_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_766_){
_start:
{
uint8_t v_stage_u2081_767_; 
v_stage_u2081_767_ = lean_ctor_get_uint8(v_m_766_, sizeof(void*)*2);
if (v_stage_u2081_767_ == 0)
{
return v_m_766_;
}
else
{
lean_object* v_map_u2081_768_; lean_object* v_map_u2082_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
v_map_u2081_768_ = lean_ctor_get(v_m_766_, 0);
v_map_u2082_769_ = lean_ctor_get(v_m_766_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_m_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v_m_766_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_map_u2082_769_);
lean_inc(v_map_u2081_768_);
lean_dec(v_m_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
uint8_t v___x_773_; lean_object* v___x_775_; 
v___x_773_ = 0;
if (v_isShared_772_ == 0)
{
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_map_u2081_768_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_map_u2082_769_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*2, v___x_773_);
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_778_, lean_object* v_m_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_array_mk(v_es_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_783_, size_t v_i_784_, size_t v_stop_785_, lean_object* v_b_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_eq(v_i_784_, v_stop_785_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; size_t v___x_790_; size_t v___x_791_; 
v___x_788_ = lean_array_uget_borrowed(v_as_783_, v_i_784_);
lean_inc(v___x_788_);
v___x_789_ = l_Lean_addAliasEntry(v_b_786_, v___x_788_);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_add(v_i_784_, v___x_790_);
v_i_784_ = v___x_791_;
v_b_786_ = v___x_789_;
goto _start;
}
else
{
return v_b_786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_793_, lean_object* v_i_794_, lean_object* v_stop_795_, lean_object* v_b_796_){
_start:
{
size_t v_i_boxed_797_; size_t v_stop_boxed_798_; lean_object* v_res_799_; 
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_stop_boxed_798_ = lean_unbox_usize(v_stop_795_);
lean_dec(v_stop_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_793_, v_i_boxed_797_, v_stop_boxed_798_, v_b_796_);
lean_dec_ref(v_as_793_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_800_, size_t v_i_801_, size_t v_stop_802_, lean_object* v_b_803_){
_start:
{
lean_object* v___y_805_; uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_eq(v_i_801_, v_stop_802_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_810_ = lean_array_uget_borrowed(v_as_800_, v_i_801_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_array_get_size(v___x_810_);
v___x_813_ = lean_nat_dec_lt(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
v___y_805_ = v_b_803_;
goto v___jp_804_;
}
else
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_le(v___x_812_, v___x_812_);
if (v___x_814_ == 0)
{
if (v___x_813_ == 0)
{
v___y_805_ = v_b_803_;
goto v___jp_804_;
}
else
{
size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; 
v___x_815_ = ((size_t)0ULL);
v___x_816_ = lean_usize_of_nat(v___x_812_);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_810_, v___x_815_, v___x_816_, v_b_803_);
v___y_805_ = v___x_817_;
goto v___jp_804_;
}
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((size_t)0ULL);
v___x_819_ = lean_usize_of_nat(v___x_812_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_810_, v___x_818_, v___x_819_, v_b_803_);
v___y_805_ = v___x_820_;
goto v___jp_804_;
}
}
}
else
{
return v_b_803_;
}
v___jp_804_:
{
size_t v___x_806_; size_t v___x_807_; 
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_801_, v___x_806_);
v_i_801_ = v___x_807_;
v_b_803_ = v___y_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_821_, lean_object* v_i_822_, lean_object* v_stop_823_, lean_object* v_b_824_){
_start:
{
size_t v_i_boxed_825_; size_t v_stop_boxed_826_; lean_object* v_res_827_; 
v_i_boxed_825_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_stop_boxed_826_ = lean_unbox_usize(v_stop_823_);
lean_dec(v_stop_823_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_821_, v_i_boxed_825_, v_stop_boxed_826_, v_b_824_);
lean_dec_ref(v_as_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_828_, lean_object* v_as_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_array_get_size(v_as_829_);
v___x_832_ = lean_nat_dec_lt(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
return v_initState_828_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_le(v___x_831_, v___x_831_);
if (v___x_833_ == 0)
{
if (v___x_832_ == 0)
{
return v_initState_828_;
}
else
{
size_t v___x_834_; size_t v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((size_t)0ULL);
v___x_835_ = lean_usize_of_nat(v___x_831_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_829_, v___x_834_, v___x_835_, v_initState_828_);
return v___x_836_;
}
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_of_nat(v___x_831_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_829_, v___x_837_, v___x_838_, v_initState_828_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_840_, lean_object* v_as_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_840_, v_as_841_);
lean_dec_ref(v_as_841_);
return v_res_842_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
v___x_844_ = lean_unsigned_to_nat(16u);
v___x_845_ = lean_mk_array(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_849_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; 
v___x_852_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_853_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_854_ = 1;
v___x_855_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_852_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*2, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l_Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l_Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_858_ = l_Lean_mkStateFromImportedEntries___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_857_, v_es_856_);
v___x_859_ = l_Lean_SMap_switch___at___00Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_860_);
lean_dec_ref(v_es_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_879_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_881_;
}
}
LEAN_EXPORT lean_object* lean_add_alias(lean_object* v_env_882_, lean_object* v_a_883_, lean_object* v_e_884_){
_start:
{
lean_object* v___x_885_; lean_object* v_toEnvExtension_886_; lean_object* v_asyncMode_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_885_ = l_Lean_aliasExtension;
v_toEnvExtension_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc_ref(v_toEnvExtension_886_);
v_asyncMode_887_ = lean_ctor_get(v_toEnvExtension_886_, 2);
lean_inc(v_asyncMode_887_);
lean_dec_ref(v_toEnvExtension_886_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_a_883_);
lean_ctor_set(v___x_888_, 1, v_e_884_);
v___x_889_ = lean_box(0);
v___x_890_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_885_, v_env_882_, v___x_888_, v_asyncMode_887_, v___x_889_);
lean_dec(v_asyncMode_887_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_894_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_895_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_894_, v___x_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_896_){
_start:
{
lean_object* v___x_897_; lean_object* v_toEnvExtension_898_; lean_object* v_asyncMode_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_897_ = l_Lean_aliasExtension;
v_toEnvExtension_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_toEnvExtension_898_);
v_asyncMode_899_ = lean_ctor_get(v_toEnvExtension_898_, 2);
lean_inc(v_asyncMode_899_);
lean_dec_ref(v_toEnvExtension_898_);
v___x_900_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_901_ = lean_box(0);
v___x_902_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_900_, v___x_897_, v_env_896_, v_asyncMode_899_, v___x_901_);
lean_dec(v_asyncMode_899_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_903_, uint8_t v_skipProtected_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
if (lean_obj_tag(v_a_905_) == 0)
{
lean_object* v___x_907_; 
lean_dec_ref(v_env_903_);
v___x_907_ = l_List_reverse___redArg(v_a_906_);
return v___x_907_;
}
else
{
lean_object* v_head_908_; lean_object* v_tail_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_920_; 
v_head_908_ = lean_ctor_get(v_a_905_, 0);
v_tail_909_ = lean_ctor_get(v_a_905_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_a_905_);
if (v_isSharedCheck_920_ == 0)
{
v___x_911_ = v_a_905_;
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_tail_909_);
lean_inc(v_head_908_);
lean_dec(v_a_905_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_913_; 
lean_inc(v_head_908_);
lean_inc_ref(v_env_903_);
v___x_913_ = l_Lean_isProtected(v_env_903_, v_head_908_);
if (v___x_913_ == 0)
{
if (v_skipProtected_904_ == 0)
{
lean_del_object(v___x_911_);
lean_dec(v_head_908_);
v_a_905_ = v_tail_909_;
goto _start;
}
else
{
lean_object* v___x_916_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v_a_906_);
v___x_916_ = v___x_911_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_head_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_a_906_);
v___x_916_ = v_reuseFailAlloc_918_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
v_a_905_ = v_tail_909_;
v_a_906_ = v___x_916_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_911_);
lean_dec(v_head_908_);
v_a_905_ = v_tail_909_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_921_, lean_object* v_skipProtected_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint8_t v_skipProtected_boxed_925_; lean_object* v_res_926_; 
v_skipProtected_boxed_925_ = lean_unbox(v_skipProtected_922_);
v_res_926_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_921_, v_skipProtected_boxed_925_, v_a_923_, v_a_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_927_, lean_object* v_a_928_, uint8_t v_skipProtected_929_){
_start:
{
lean_object* v___x_930_; lean_object* v_toEnvExtension_931_; lean_object* v_asyncMode_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_930_ = l_Lean_aliasExtension;
v_toEnvExtension_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_toEnvExtension_931_);
v_asyncMode_932_ = lean_ctor_get(v_toEnvExtension_931_, 2);
lean_inc(v_asyncMode_932_);
lean_dec_ref(v_toEnvExtension_931_);
v___x_933_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_934_ = lean_box(0);
lean_inc_ref(v_env_927_);
v___x_935_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_933_, v___x_930_, v_env_927_, v_asyncMode_932_, v___x_934_);
lean_dec(v_asyncMode_932_);
v___x_936_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_935_, v_a_928_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_937_; 
lean_dec_ref(v_env_927_);
v___x_937_ = lean_box(0);
return v___x_937_;
}
else
{
if (v_skipProtected_929_ == 0)
{
lean_object* v_val_938_; 
lean_dec_ref(v_env_927_);
v_val_938_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_938_);
lean_dec_ref(v___x_936_);
return v_val_938_;
}
else
{
lean_object* v_val_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_val_939_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_939_);
lean_dec_ref(v___x_936_);
v___x_940_ = lean_box(0);
v___x_941_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_927_, v_skipProtected_929_, v_val_939_, v___x_940_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_942_, lean_object* v_a_943_, lean_object* v_skipProtected_944_){
_start:
{
uint8_t v_skipProtected_boxed_945_; lean_object* v_res_946_; 
v_skipProtected_boxed_945_ = lean_unbox(v_skipProtected_944_);
v_res_946_ = l_Lean_getAliases(v_env_942_, v_a_943_, v_skipProtected_boxed_945_);
lean_dec(v_a_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_947_, lean_object* v_as_948_, lean_object* v_a_949_, lean_object* v_es_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_947_, v_es_950_);
if (v___x_951_ == 0)
{
lean_dec(v_a_949_);
return v_as_948_;
}
else
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_952_, 0, v_a_949_);
lean_ctor_set(v___x_952_, 1, v_as_948_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_953_, lean_object* v_as_954_, lean_object* v_a_955_, lean_object* v_es_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_getRevAliases___lam__0(v_e_953_, v_as_954_, v_a_955_, v_es_956_);
lean_dec(v_es_956_);
lean_dec(v_e_953_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_i_961_, lean_object* v_acc_962_){
_start:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_get_size(v_keys_959_);
v___x_964_ = lean_nat_dec_lt(v_i_961_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec(v_i_961_);
lean_dec(v_f_958_);
return v_acc_962_;
}
else
{
lean_object* v_k_965_; lean_object* v_v_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_k_965_ = lean_array_fget_borrowed(v_keys_959_, v_i_961_);
v_v_966_ = lean_array_fget_borrowed(v_vals_960_, v_i_961_);
lean_inc(v_f_958_);
lean_inc(v_v_966_);
lean_inc(v_k_965_);
v___x_967_ = lean_apply_3(v_f_958_, v_acc_962_, v_k_965_, v_v_966_);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_i_961_, v___x_968_);
lean_dec(v_i_961_);
v_i_961_ = v___x_969_;
v_acc_962_ = v___x_967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_i_974_, lean_object* v_acc_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_971_, v_keys_972_, v_vals_973_, v_i_974_, v_acc_975_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_978_) == 0)
{
lean_object* v_es_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_es_980_ = lean_ctor_get(v_x_978_, 0);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_array_get_size(v_es_980_);
v___x_983_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec(v_f_977_);
return v_x_979_;
}
else
{
uint8_t v___x_984_; 
v___x_984_ = lean_nat_dec_le(v___x_982_, v___x_982_);
if (v___x_984_ == 0)
{
if (v___x_983_ == 0)
{
lean_dec(v_f_977_);
return v_x_979_;
}
else
{
size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
v___x_985_ = ((size_t)0ULL);
v___x_986_ = lean_usize_of_nat(v___x_982_);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_977_, v_es_980_, v___x_985_, v___x_986_, v_x_979_);
return v___x_987_;
}
}
else
{
size_t v___x_988_; size_t v___x_989_; lean_object* v___x_990_; 
v___x_988_ = ((size_t)0ULL);
v___x_989_ = lean_usize_of_nat(v___x_982_);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_977_, v_es_980_, v___x_988_, v___x_989_, v_x_979_);
return v___x_990_;
}
}
}
else
{
lean_object* v_ks_991_; lean_object* v_vs_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_ks_991_ = lean_ctor_get(v_x_978_, 0);
v_vs_992_ = lean_ctor_get(v_x_978_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_977_, v_ks_991_, v_vs_992_, v___x_993_, v_x_979_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_995_, lean_object* v_as_996_, size_t v_i_997_, size_t v_stop_998_, lean_object* v_b_999_){
_start:
{
lean_object* v___y_1001_; uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_eq(v_i_997_, v_stop_998_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_array_uget_borrowed(v_as_996_, v_i_997_);
switch(lean_obj_tag(v___x_1006_))
{
case 0:
{
lean_object* v_key_1007_; lean_object* v_val_1008_; lean_object* v___x_1009_; 
v_key_1007_ = lean_ctor_get(v___x_1006_, 0);
v_val_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_f_995_);
lean_inc(v_val_1008_);
lean_inc(v_key_1007_);
v___x_1009_ = lean_apply_3(v_f_995_, v_b_999_, v_key_1007_, v_val_1008_);
v___y_1001_ = v___x_1009_;
goto v___jp_1000_;
}
case 1:
{
lean_object* v_node_1010_; lean_object* v___x_1011_; 
v_node_1010_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_f_995_);
v___x_1011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_995_, v_node_1010_, v_b_999_);
v___y_1001_ = v___x_1011_;
goto v___jp_1000_;
}
default: 
{
v___y_1001_ = v_b_999_;
goto v___jp_1000_;
}
}
}
else
{
lean_dec(v_f_995_);
return v_b_999_;
}
v___jp_1000_:
{
size_t v___x_1002_; size_t v___x_1003_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_997_, v___x_1002_);
v_i_997_ = v___x_1003_;
v_b_999_ = v___y_1001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_1012_, lean_object* v_as_1013_, lean_object* v_i_1014_, lean_object* v_stop_1015_, lean_object* v_b_1016_){
_start:
{
size_t v_i_boxed_1017_; size_t v_stop_boxed_1018_; lean_object* v_res_1019_; 
v_i_boxed_1017_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_stop_boxed_1018_ = lean_unbox_usize(v_stop_1015_);
lean_dec(v_stop_1015_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1012_, v_as_1013_, v_i_boxed_1017_, v_stop_boxed_1018_, v_b_1016_);
lean_dec_ref(v_as_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1020_, v_x_1021_, v_x_1022_);
lean_dec_ref(v_x_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1024_, lean_object* v_x1_1025_, lean_object* v_x2_1026_, lean_object* v_x3_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_apply_3(v_f_1024_, v_x1_1025_, v_x2_1026_, v_x3_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1029_, lean_object* v_f_1030_, lean_object* v_init_1031_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; 
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1032_, 0, v_f_1030_);
v___x_1033_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1032_, v_map_1029_, v_init_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1034_, lean_object* v_f_1035_, lean_object* v_init_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1034_, v_f_1035_, v_init_1036_);
lean_dec_ref(v_map_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
if (lean_obj_tag(v_x_1040_) == 0)
{
lean_dec(v_f_1038_);
return v_x_1039_;
}
else
{
lean_object* v_key_1041_; lean_object* v_value_1042_; lean_object* v_tail_1043_; lean_object* v___x_1044_; 
v_key_1041_ = lean_ctor_get(v_x_1040_, 0);
lean_inc(v_key_1041_);
v_value_1042_ = lean_ctor_get(v_x_1040_, 1);
lean_inc(v_value_1042_);
v_tail_1043_ = lean_ctor_get(v_x_1040_, 2);
lean_inc(v_tail_1043_);
lean_dec_ref(v_x_1040_);
lean_inc(v_f_1038_);
v___x_1044_ = lean_apply_3(v_f_1038_, v_x_1039_, v_key_1041_, v_value_1042_);
v_x_1039_ = v___x_1044_;
v_x_1040_ = v_tail_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1046_, lean_object* v_as_1047_, size_t v_i_1048_, size_t v_stop_1049_, lean_object* v_b_1050_){
_start:
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_usize_dec_eq(v_i_1048_, v_stop_1049_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; 
v___x_1052_ = lean_array_uget_borrowed(v_as_1047_, v_i_1048_);
lean_inc(v___x_1052_);
lean_inc(v_f_1046_);
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1046_, v_b_1050_, v___x_1052_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1048_, v___x_1054_);
v_i_1048_ = v___x_1055_;
v_b_1050_ = v___x_1053_;
goto _start;
}
else
{
lean_dec(v_f_1046_);
return v_b_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1057_, lean_object* v_as_1058_, lean_object* v_i_1059_, lean_object* v_stop_1060_, lean_object* v_b_1061_){
_start:
{
size_t v_i_boxed_1062_; size_t v_stop_boxed_1063_; lean_object* v_res_1064_; 
v_i_boxed_1062_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_stop_boxed_1063_ = lean_unbox_usize(v_stop_1060_);
lean_dec(v_stop_1060_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1057_, v_as_1058_, v_i_boxed_1062_, v_stop_boxed_1063_, v_b_1061_);
lean_dec_ref(v_as_1058_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1065_, lean_object* v_init_1066_, lean_object* v_m_1067_){
_start:
{
lean_object* v_map_u2081_1068_; lean_object* v_map_u2082_1069_; lean_object* v_buckets_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_map_u2081_1068_ = lean_ctor_get(v_m_1067_, 0);
v_map_u2082_1069_ = lean_ctor_get(v_m_1067_, 1);
v_buckets_1070_ = lean_ctor_get(v_map_u2081_1068_, 1);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_array_get_size(v_buckets_1070_);
v___x_1073_ = lean_nat_dec_lt(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1069_, v_f_1065_, v_init_1066_);
return v___x_1074_;
}
else
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_nat_dec_le(v___x_1072_, v___x_1072_);
if (v___x_1075_ == 0)
{
if (v___x_1073_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1069_, v_f_1065_, v_init_1066_);
return v___x_1076_;
}
else
{
size_t v___x_1077_; size_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = ((size_t)0ULL);
v___x_1078_ = lean_usize_of_nat(v___x_1072_);
lean_inc(v_f_1065_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1065_, v_buckets_1070_, v___x_1077_, v___x_1078_, v_init_1066_);
v___x_1080_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1069_, v_f_1065_, v___x_1079_);
return v___x_1080_;
}
}
else
{
size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1072_);
lean_inc(v_f_1065_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1065_, v_buckets_1070_, v___x_1081_, v___x_1082_, v_init_1066_);
v___x_1084_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1069_, v_f_1065_, v___x_1083_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1085_, lean_object* v_init_1086_, lean_object* v_m_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1085_, v_init_1086_, v_m_1087_);
lean_dec_ref(v_m_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1089_, lean_object* v_e_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v_toEnvExtension_1092_; lean_object* v_asyncMode_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1091_ = l_Lean_aliasExtension;
v_toEnvExtension_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_toEnvExtension_1092_);
v_asyncMode_1093_ = lean_ctor_get(v_toEnvExtension_1092_, 2);
lean_inc(v_asyncMode_1093_);
lean_dec_ref(v_toEnvExtension_1092_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1094_, 0, v_e_1090_);
v___x_1095_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1095_, v___x_1091_, v_env_1089_, v_asyncMode_1093_, v___x_1097_);
lean_dec(v_asyncMode_1093_);
v___x_1099_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1094_, v___x_1096_, v___x_1098_);
lean_dec(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1100_, lean_object* v_00_u03c3_1101_, lean_object* v_f_1102_, lean_object* v_init_1103_, lean_object* v_m_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1102_, v_init_1103_, v_m_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_00_u03c3_1107_, lean_object* v_f_1108_, lean_object* v_init_1109_, lean_object* v_m_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1106_, v_00_u03c3_1107_, v_f_1108_, v_init_1109_, v_m_1110_);
lean_dec_ref(v_m_1110_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1112_, lean_object* v_00_u03c3_1113_, lean_object* v_f_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1114_, v_x_1115_, v_x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_map_1120_, lean_object* v_f_1121_, lean_object* v_init_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1120_, v_f_1121_, v_init_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_map_1126_, lean_object* v_f_1127_, lean_object* v_init_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1124_, v_00_u03b2_1125_, v_map_1126_, v_f_1127_, v_init_1128_);
lean_dec_ref(v_map_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1130_, lean_object* v_00_u03c3_1131_, lean_object* v_f_1132_, lean_object* v_as_1133_, size_t v_i_1134_, size_t v_stop_1135_, lean_object* v_b_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1132_, v_as_1133_, v_i_1134_, v_stop_1135_, v_b_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1138_, lean_object* v_00_u03c3_1139_, lean_object* v_f_1140_, lean_object* v_as_1141_, lean_object* v_i_1142_, lean_object* v_stop_1143_, lean_object* v_b_1144_){
_start:
{
size_t v_i_boxed_1145_; size_t v_stop_boxed_1146_; lean_object* v_res_1147_; 
v_i_boxed_1145_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_stop_boxed_1146_ = lean_unbox_usize(v_stop_1143_);
lean_dec(v_stop_1143_);
v_res_1147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1138_, v_00_u03c3_1139_, v_f_1140_, v_as_1141_, v_i_boxed_1145_, v_stop_boxed_1146_, v_b_1144_);
lean_dec_ref(v_as_1141_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1148_, lean_object* v_f_1149_, lean_object* v_init_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1149_, v_map_1148_, v_init_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1152_, lean_object* v_f_1153_, lean_object* v_init_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1152_, v_f_1153_, v_init_1154_);
lean_dec_ref(v_map_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1156_, lean_object* v_00_u03b2_1157_, lean_object* v_map_1158_, lean_object* v_f_1159_, lean_object* v_init_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1159_, v_map_1158_, v_init_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_map_1164_, lean_object* v_f_1165_, lean_object* v_init_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1162_, v_00_u03b2_1163_, v_map_1164_, v_f_1165_, v_init_1166_);
lean_dec_ref(v_map_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1168_, lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_f_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1171_, v_x_1172_, v_x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1175_, lean_object* v_00_u03b1_1176_, lean_object* v_00_u03b2_1177_, lean_object* v_f_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1175_, v_00_u03b1_1176_, v_00_u03b2_1177_, v_f_1178_, v_x_1179_, v_x_1180_);
lean_dec_ref(v_x_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_00_u03c3_1184_, lean_object* v_f_1185_, lean_object* v_as_1186_, size_t v_i_1187_, size_t v_stop_1188_, lean_object* v_b_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1185_, v_as_1186_, v_i_1187_, v_stop_1188_, v_b_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_00_u03c3_1193_, lean_object* v_f_1194_, lean_object* v_as_1195_, lean_object* v_i_1196_, lean_object* v_stop_1197_, lean_object* v_b_1198_){
_start:
{
size_t v_i_boxed_1199_; size_t v_stop_boxed_1200_; lean_object* v_res_1201_; 
v_i_boxed_1199_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_stop_boxed_1200_ = lean_unbox_usize(v_stop_1197_);
lean_dec(v_stop_1197_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1191_, v_00_u03b2_1192_, v_00_u03c3_1193_, v_f_1194_, v_as_1195_, v_i_boxed_1199_, v_stop_boxed_1200_, v_b_1198_);
lean_dec_ref(v_as_1195_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_f_1205_, lean_object* v_keys_1206_, lean_object* v_vals_1207_, lean_object* v_heq_1208_, lean_object* v_i_1209_, lean_object* v_acc_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1205_, v_keys_1206_, v_vals_1207_, v_i_1209_, v_acc_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1212_, lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_f_1215_, lean_object* v_keys_1216_, lean_object* v_vals_1217_, lean_object* v_heq_1218_, lean_object* v_i_1219_, lean_object* v_acc_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1212_, v_00_u03b1_1213_, v_00_u03b2_1214_, v_f_1215_, v_keys_1216_, v_vals_1217_, v_heq_1218_, v_i_1219_, v_acc_1220_);
lean_dec_ref(v_vals_1217_);
lean_dec_ref(v_keys_1216_);
return v_res_1221_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1222_, lean_object* v_declName_1223_){
_start:
{
uint8_t v___y_1225_; uint8_t v___x_1228_; 
lean_inc_ref(v_env_1222_);
v___x_1228_ = l_Lean_Environment_containsOnBranch(v_env_1222_, v_declName_1223_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; 
lean_inc(v_declName_1223_);
lean_inc_ref(v_env_1222_);
v___x_1229_ = lean_is_reserved_name(v_env_1222_, v_declName_1223_);
v___y_1225_ = v___x_1229_;
goto v___jp_1224_;
}
else
{
v___y_1225_ = v___x_1228_;
goto v___jp_1224_;
}
v___jp_1224_:
{
if (v___y_1225_ == 0)
{
uint8_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 1;
v___x_1227_ = l_Lean_Environment_contains(v_env_1222_, v_declName_1223_, v___x_1226_);
return v___x_1227_;
}
else
{
lean_dec(v_declName_1223_);
lean_dec_ref(v_env_1222_);
return v___y_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1230_, lean_object* v_declName_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1230_, v_declName_1231_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1234_, lean_object* v_decl_1235_, lean_object* v_ref_1236_){
_start:
{
lean_object* v_defValue_1238_; lean_object* v_descr_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1266_; 
v_defValue_1238_ = lean_ctor_get(v_decl_1235_, 0);
v_descr_1239_ = lean_ctor_get(v_decl_1235_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_decl_1235_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1241_ = v_decl_1235_;
v_isShared_1242_ = v_isSharedCheck_1266_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_descr_1239_);
lean_inc(v_defValue_1238_);
lean_dec(v_decl_1235_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1266_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_alloc_ctor(1, 0, 1);
v___x_1244_ = lean_unbox(v_defValue_1238_);
lean_ctor_set_uint8(v___x_1243_, 0, v___x_1244_);
lean_inc(v_name_1234_);
v___x_1245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1245_, 0, v_name_1234_);
lean_ctor_set(v___x_1245_, 1, v_ref_1236_);
lean_ctor_set(v___x_1245_, 2, v___x_1243_);
lean_ctor_set(v___x_1245_, 3, v_descr_1239_);
lean_inc(v_name_1234_);
v___x_1246_ = lean_register_option(v_name_1234_, v___x_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1246_, 0);
lean_dec(v_unused_1257_);
v___x_1248_ = v___x_1246_;
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v___x_1246_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_defValue_1238_);
lean_ctor_set(v___x_1241_, 0, v_name_1234_);
v___x_1251_ = v___x_1241_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_name_1234_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_defValue_1238_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1251_);
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1241_);
lean_dec(v_defValue_1238_);
lean_dec(v_name_1234_);
v_a_1258_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1246_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1246_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1267_, lean_object* v_decl_1268_, lean_object* v_ref_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1267_, v_decl_1268_, v_ref_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = ((lean_object*)(l_Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1290_ = ((lean_object*)(l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1291_ = ((lean_object*)(l_Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1292_ = l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1289_, v___x_1290_, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l_Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1313_ = ((lean_object*)(l_Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1314_ = ((lean_object*)(l_Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1315_ = l_Lean_Option_register___at___00Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1312_, v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1318_, lean_object* v_opt_1319_){
_start:
{
lean_object* v_name_1320_; lean_object* v_defValue_1321_; lean_object* v_map_1322_; lean_object* v___x_1323_; 
v_name_1320_ = lean_ctor_get(v_opt_1319_, 0);
v_defValue_1321_ = lean_ctor_get(v_opt_1319_, 1);
v_map_1322_ = lean_ctor_get(v_opts_1318_, 0);
v___x_1323_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1322_, v_name_1320_);
if (lean_obj_tag(v___x_1323_) == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_unbox(v_defValue_1321_);
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; 
v_val_1325_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1325_);
lean_dec_ref(v___x_1323_);
if (lean_obj_tag(v_val_1325_) == 1)
{
uint8_t v_v_1326_; 
v_v_1326_ = lean_ctor_get_uint8(v_val_1325_, 0);
lean_dec_ref(v_val_1325_);
return v_v_1326_;
}
else
{
uint8_t v___x_1327_; 
lean_dec(v_val_1325_);
v___x_1327_ = lean_unbox(v_defValue_1321_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1328_, lean_object* v_opt_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1328_, v_opt_1329_);
lean_dec_ref(v_opt_1329_);
lean_dec_ref(v_opts_1328_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1335_, lean_object* v_env_1336_, lean_object* v_as_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_b_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v_env_1336_);
lean_dec(v_declName_1335_);
return v_b_1340_;
}
else
{
lean_object* v_a_1342_; lean_object* v_toImport_1343_; lean_object* v_module_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
lean_dec_ref(v_b_1340_);
v_a_1342_ = lean_array_uget_borrowed(v_as_1337_, v_i_1339_);
v_toImport_1343_ = lean_ctor_get(v_a_1342_, 0);
v_module_1344_ = lean_ctor_get(v_toImport_1343_, 0);
v___x_1345_ = lean_box(0);
lean_inc(v_declName_1335_);
lean_inc(v_module_1344_);
v___x_1346_ = l_Lean_mkPrivateNameCore(v_module_1344_, v_declName_1335_);
lean_inc(v___x_1346_);
lean_inc_ref(v_env_1336_);
v___x_1347_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1336_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; 
lean_dec(v___x_1346_);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_add(v_i_1339_, v___x_1349_);
v_i_1339_ = v___x_1350_;
v_b_1340_ = v___x_1348_;
goto _start;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v_env_1336_);
lean_dec(v_declName_1335_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1346_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1345_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1355_, lean_object* v_env_1356_, lean_object* v_as_1357_, lean_object* v_sz_1358_, lean_object* v_i_1359_, lean_object* v_b_1360_){
_start:
{
size_t v_sz_boxed_1361_; size_t v_i_boxed_1362_; lean_object* v_res_1363_; 
v_sz_boxed_1361_ = lean_unbox_usize(v_sz_1358_);
lean_dec(v_sz_1358_);
v_i_boxed_1362_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1355_, v_env_1356_, v_as_1357_, v_sz_boxed_1361_, v_i_boxed_1362_, v_b_1360_);
lean_dec_ref(v_as_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1364_, lean_object* v_opts_1365_, lean_object* v_declName_1366_){
_start:
{
uint8_t v_isExporting_1382_; 
v_isExporting_1382_ = lean_ctor_get_uint8(v_env_1364_, sizeof(void*)*8);
if (v_isExporting_1382_ == 0)
{
goto v___jp_1367_;
}
else
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1384_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1365_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec(v_declName_1366_);
lean_dec_ref(v_env_1364_);
v___x_1385_ = lean_box(0);
return v___x_1385_;
}
else
{
goto v___jp_1367_;
}
}
v___jp_1367_:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
lean_inc(v_declName_1366_);
v___x_1368_ = l_Lean_mkPrivateName(v_env_1364_, v_declName_1366_);
lean_inc(v___x_1368_);
lean_inc_ref(v_env_1364_);
v___x_1369_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1364_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; uint8_t v_isModule_1371_; 
lean_dec(v___x_1368_);
v___x_1370_ = l_Lean_Environment_header(v_env_1364_);
v_isModule_1371_ = lean_ctor_get_uint8(v___x_1370_, sizeof(void*)*7 + 4);
if (v_isModule_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v___x_1370_);
lean_dec(v_declName_1366_);
lean_dec_ref(v_env_1364_);
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
else
{
lean_object* v_importAllModules_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; lean_object* v_fst_1379_; 
v_importAllModules_1373_ = lean_ctor_get(v___x_1370_, 5);
lean_inc_ref(v_importAllModules_1373_);
lean_dec_ref(v___x_1370_);
v___x_1374_ = lean_box(0);
v___x_1375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1376_ = lean_array_size(v_importAllModules_1373_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1366_, v_env_1364_, v_importAllModules_1373_, v_sz_1376_, v___x_1377_, v___x_1375_);
lean_dec_ref(v_importAllModules_1373_);
v_fst_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fst_1379_);
lean_dec_ref(v___x_1378_);
if (lean_obj_tag(v_fst_1379_) == 0)
{
return v___x_1374_;
}
else
{
lean_object* v_val_1380_; 
v_val_1380_ = lean_ctor_get(v_fst_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref(v_fst_1379_);
return v_val_1380_;
}
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v_declName_1366_);
lean_dec_ref(v_env_1364_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1368_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1386_, lean_object* v_opts_1387_, lean_object* v_declName_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1386_, v_opts_1387_, v_declName_1388_);
lean_dec_ref(v_opts_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1390_, lean_object* v_opts_1391_, lean_object* v_ns_1392_, lean_object* v_id_1393_){
_start:
{
lean_object* v_resolvedId_1394_; uint8_t v___x_1395_; lean_object* v_resolvedIds_1396_; 
lean_inc(v_id_1393_);
v_resolvedId_1394_ = l_Lean_Name_append(v_ns_1392_, v_id_1393_);
v___x_1395_ = l_Lean_Name_isAtomic(v_id_1393_);
lean_dec(v_id_1393_);
lean_inc_ref(v_env_1390_);
v_resolvedIds_1396_ = l_Lean_getAliases(v_env_1390_, v_resolvedId_1394_, v___x_1395_);
if (v___x_1395_ == 0)
{
goto v___jp_1397_;
}
else
{
uint8_t v___x_1403_; 
lean_inc(v_resolvedId_1394_);
lean_inc_ref(v_env_1390_);
v___x_1403_ = l_Lean_isProtected(v_env_1390_, v_resolvedId_1394_);
if (v___x_1403_ == 0)
{
goto v___jp_1397_;
}
else
{
lean_dec(v_resolvedId_1394_);
lean_dec_ref(v_env_1390_);
return v_resolvedIds_1396_;
}
}
v___jp_1397_:
{
uint8_t v___x_1398_; 
lean_inc(v_resolvedId_1394_);
lean_inc_ref(v_env_1390_);
v___x_1398_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1390_, v_resolvedId_1394_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1390_, v_opts_1391_, v_resolvedId_1394_);
if (lean_obj_tag(v___x_1399_) == 1)
{
lean_object* v_val_1400_; lean_object* v___x_1401_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref(v___x_1399_);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_val_1400_);
lean_ctor_set(v___x_1401_, 1, v_resolvedIds_1396_);
return v___x_1401_;
}
else
{
lean_dec(v___x_1399_);
return v_resolvedIds_1396_;
}
}
else
{
lean_object* v___x_1402_; 
lean_dec_ref(v_env_1390_);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_resolvedId_1394_);
lean_ctor_set(v___x_1402_, 1, v_resolvedIds_1396_);
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1404_, lean_object* v_opts_1405_, lean_object* v_ns_1406_, lean_object* v_id_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1404_, v_opts_1405_, v_ns_1406_, v_id_1407_);
lean_dec_ref(v_opts_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1409_, lean_object* v_opts_1410_, lean_object* v_id_1411_, lean_object* v_x_1412_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 1)
{
lean_object* v_pre_1413_; lean_object* v___x_1414_; 
v_pre_1413_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_pre_1413_);
lean_inc(v_id_1411_);
lean_inc_ref(v_env_1409_);
v___x_1414_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1409_, v_opts_1410_, v_x_1412_, v_id_1411_);
if (lean_obj_tag(v___x_1414_) == 0)
{
v_x_1412_ = v_pre_1413_;
goto _start;
}
else
{
lean_dec(v_pre_1413_);
lean_dec(v_id_1411_);
lean_dec_ref(v_env_1409_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1416_; 
lean_dec(v_x_1412_);
lean_dec(v_id_1411_);
lean_dec_ref(v_env_1409_);
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1417_, lean_object* v_opts_1418_, lean_object* v_id_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1417_, v_opts_1418_, v_id_1419_, v_x_1420_);
lean_dec_ref(v_opts_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1422_, lean_object* v_opts_1423_, lean_object* v_id_1424_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_Name_isAtomic(v_id_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_resolvedId_1428_; uint8_t v___x_1429_; 
v___x_1426_ = l_Lean_rootNamespace;
v___x_1427_ = lean_box(0);
v_resolvedId_1428_ = l_Lean_Name_replacePrefix(v_id_1424_, v___x_1426_, v___x_1427_);
lean_inc(v_resolvedId_1428_);
lean_inc_ref(v_env_1422_);
v___x_1429_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1422_, v_resolvedId_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1422_, v_opts_1423_, v_resolvedId_1428_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; 
lean_dec_ref(v_env_1422_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_resolvedId_1428_);
return v___x_1431_;
}
}
else
{
lean_object* v___x_1432_; 
lean_dec(v_id_1424_);
lean_dec_ref(v_env_1422_);
v___x_1432_ = lean_box(0);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1433_, lean_object* v_opts_1434_, lean_object* v_id_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1433_, v_opts_1434_, v_id_1435_);
lean_dec_ref(v_opts_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1437_, lean_object* v_opts_1438_, lean_object* v_id_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
lean_dec(v_id_1439_);
lean_dec_ref(v_env_1437_);
return v_x_1441_;
}
else
{
lean_object* v_head_1442_; 
v_head_1442_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_head_1442_);
if (lean_obj_tag(v_head_1442_) == 0)
{
lean_object* v_tail_1443_; lean_object* v_ns_1444_; lean_object* v_except_1445_; uint8_t v___x_1446_; 
v_tail_1443_ = lean_ctor_get(v_x_1440_, 1);
lean_inc(v_tail_1443_);
lean_dec_ref(v_x_1440_);
v_ns_1444_ = lean_ctor_get(v_head_1442_, 0);
lean_inc(v_ns_1444_);
v_except_1445_ = lean_ctor_get(v_head_1442_, 1);
lean_inc(v_except_1445_);
lean_dec_ref(v_head_1442_);
v___x_1446_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1439_, v_except_1445_);
lean_dec(v_except_1445_);
if (v___x_1446_ == 0)
{
lean_object* v_newResolvedIds_1447_; lean_object* v___x_1448_; 
lean_inc(v_id_1439_);
lean_inc_ref(v_env_1437_);
v_newResolvedIds_1447_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1437_, v_opts_1438_, v_ns_1444_, v_id_1439_);
v___x_1448_ = l_List_appendTR___redArg(v_newResolvedIds_1447_, v_x_1441_);
v_x_1440_ = v_tail_1443_;
v_x_1441_ = v___x_1448_;
goto _start;
}
else
{
lean_dec(v_ns_1444_);
v_x_1440_ = v_tail_1443_;
goto _start;
}
}
else
{
lean_object* v_tail_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1471_; 
v_tail_1451_ = lean_ctor_get(v_x_1440_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1440_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_x_1440_, 0);
lean_dec(v_unused_1472_);
v___x_1453_ = v_x_1440_;
v_isShared_1454_ = v_isSharedCheck_1471_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_tail_1451_);
lean_dec(v_x_1440_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1471_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_id_1455_; lean_object* v_declName_1456_; uint8_t v___x_1457_; 
v_id_1455_ = lean_ctor_get(v_head_1442_, 0);
lean_inc(v_id_1455_);
v_declName_1456_ = lean_ctor_get(v_head_1442_, 1);
lean_inc(v_declName_1456_);
lean_dec_ref(v_head_1442_);
v___x_1457_ = lean_name_eq(v_id_1455_, v_id_1439_);
if (v___x_1457_ == 0)
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Lean_Name_isPrefixOf(v_id_1455_, v_id_1439_);
if (v___x_1458_ == 0)
{
lean_dec(v_declName_1456_);
lean_dec(v_id_1455_);
lean_del_object(v___x_1453_);
v_x_1440_ = v_tail_1451_;
goto _start;
}
else
{
lean_object* v_candidate_1460_; uint8_t v___x_1461_; 
lean_inc(v_id_1439_);
v_candidate_1460_ = l_Lean_Name_replacePrefix(v_id_1439_, v_id_1455_, v_declName_1456_);
lean_dec(v_declName_1456_);
lean_dec(v_id_1455_);
lean_inc(v_candidate_1460_);
lean_inc_ref(v_env_1437_);
v___x_1461_ = l_Lean_Environment_contains(v_env_1437_, v_candidate_1460_, v___x_1458_);
if (v___x_1461_ == 0)
{
lean_dec(v_candidate_1460_);
lean_del_object(v___x_1453_);
v_x_1440_ = v_tail_1451_;
goto _start;
}
else
{
lean_object* v___x_1464_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_x_1441_);
lean_ctor_set(v___x_1453_, 0, v_candidate_1460_);
v___x_1464_ = v___x_1453_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_candidate_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_x_1441_);
v___x_1464_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_x_1440_ = v_tail_1451_;
v_x_1441_ = v___x_1464_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1468_; 
lean_dec(v_id_1455_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_x_1441_);
lean_ctor_set(v___x_1453_, 0, v_declName_1456_);
v___x_1468_ = v___x_1453_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_declName_1456_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_x_1441_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
v_x_1440_ = v_tail_1451_;
v_x_1441_ = v___x_1468_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1473_, lean_object* v_opts_1474_, lean_object* v_id_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1473_, v_opts_1474_, v_id_1475_, v_x_1476_, v_x_1477_);
lean_dec_ref(v_opts_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1480_){
_start:
{
lean_object* v___f_1481_; lean_object* v___x_1482_; 
v___f_1481_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1482_ = l_List_eraseDupsBy___redArg(v___f_1481_, v_as_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
if (lean_obj_tag(v_a_1484_) == 0)
{
lean_object* v___x_1486_; 
lean_dec(v_projs_1483_);
v___x_1486_ = l_List_reverse___redArg(v_a_1485_);
return v___x_1486_;
}
else
{
lean_object* v_head_1487_; lean_object* v_tail_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1497_; 
v_head_1487_ = lean_ctor_get(v_a_1484_, 0);
v_tail_1488_ = lean_ctor_get(v_a_1484_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1484_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1490_ = v_a_1484_;
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_tail_1488_);
lean_inc(v_head_1487_);
lean_dec(v_a_1484_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_inc(v_projs_1483_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_head_1487_);
lean_ctor_set(v___x_1492_, 1, v_projs_1483_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_a_1485_);
lean_ctor_set(v___x_1490_, 0, v___x_1492_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_a_1485_);
v___x_1494_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
v_a_1484_ = v_tail_1488_;
v_a_1485_ = v___x_1494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1498_, lean_object* v_opts_1499_, lean_object* v_ns_1500_, lean_object* v_openDecls_1501_, lean_object* v_extractionResult_1502_, lean_object* v_id_1503_, lean_object* v_projs_1504_){
_start:
{
if (lean_obj_tag(v_id_1503_) == 1)
{
lean_object* v_pre_1505_; lean_object* v_str_1506_; lean_object* v_imported_1507_; lean_object* v_ctx_1508_; lean_object* v_scopes_1509_; lean_object* v___x_1510_; lean_object* v_id_1511_; lean_object* v___y_1513_; lean_object* v___x_1523_; lean_object* v___y_1525_; 
v_pre_1505_ = lean_ctor_get(v_id_1503_, 0);
lean_inc(v_pre_1505_);
v_str_1506_ = lean_ctor_get(v_id_1503_, 1);
lean_inc_ref(v_str_1506_);
v_imported_1507_ = lean_ctor_get(v_extractionResult_1502_, 1);
v_ctx_1508_ = lean_ctor_get(v_extractionResult_1502_, 2);
v_scopes_1509_ = lean_ctor_get(v_extractionResult_1502_, 3);
lean_inc(v_scopes_1509_);
lean_inc(v_ctx_1508_);
lean_inc(v_imported_1507_);
v___x_1510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1510_, 0, v_id_1503_);
lean_ctor_set(v___x_1510_, 1, v_imported_1507_);
lean_ctor_set(v___x_1510_, 2, v_ctx_1508_);
lean_ctor_set(v___x_1510_, 3, v_scopes_1509_);
v_id_1511_ = l_Lean_MacroScopesView_review(v___x_1510_);
lean_inc(v_ns_1500_);
lean_inc(v_id_1511_);
lean_inc_ref(v_env_1498_);
v___x_1523_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1498_, v_opts_1499_, v_id_1511_, v_ns_1500_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_id_1511_);
lean_inc_ref(v_env_1498_);
v___x_1530_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1498_, v_opts_1499_, v_id_1511_);
if (lean_obj_tag(v___x_1530_) == 0)
{
uint8_t v___x_1531_; 
lean_inc(v_id_1511_);
lean_inc_ref(v_env_1498_);
v___x_1531_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1498_, v_id_1511_);
if (v___x_1531_ == 0)
{
v___y_1525_ = v___x_1523_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1532_; 
lean_inc(v_id_1511_);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_id_1511_);
lean_ctor_set(v___x_1532_, 1, v___x_1523_);
v___y_1525_ = v___x_1532_;
goto v___jp_1524_;
}
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_id_1511_);
lean_dec_ref(v_str_1506_);
lean_dec(v_pre_1505_);
lean_dec(v_openDecls_1501_);
lean_dec(v_ns_1500_);
lean_dec_ref(v_env_1498_);
v_val_1533_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1533_);
lean_dec_ref(v___x_1530_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_val_1533_);
lean_ctor_set(v___x_1534_, 1, v_projs_1504_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
return v___x_1536_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_id_1511_);
lean_dec_ref(v_str_1506_);
lean_dec(v_pre_1505_);
lean_dec(v_openDecls_1501_);
lean_dec(v_ns_1500_);
lean_dec_ref(v_env_1498_);
v___x_1537_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1523_);
v___x_1538_ = lean_box(0);
v___x_1539_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1504_, v___x_1537_, v___x_1538_);
return v___x_1539_;
}
v___jp_1512_:
{
lean_object* v_resolvedIds_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v_resolvedIds_1517_; 
lean_inc(v_openDecls_1501_);
lean_inc(v_id_1511_);
lean_inc_ref(v_env_1498_);
v_resolvedIds_1514_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1498_, v_opts_1499_, v_id_1511_, v_openDecls_1501_, v___y_1513_);
v___x_1515_ = l_Lean_Name_isAtomic(v_id_1511_);
lean_inc_ref(v_env_1498_);
v___x_1516_ = l_Lean_getAliases(v_env_1498_, v_id_1511_, v___x_1515_);
lean_dec(v_id_1511_);
v_resolvedIds_1517_ = l_List_appendTR___redArg(v___x_1516_, v_resolvedIds_1514_);
if (lean_obj_tag(v_resolvedIds_1517_) == 0)
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_str_1506_);
lean_ctor_set(v___x_1518_, 1, v_projs_1504_);
v_id_1503_ = v_pre_1505_;
v_projs_1504_ = v___x_1518_;
goto _start;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v_str_1506_);
lean_dec(v_pre_1505_);
lean_dec(v_openDecls_1501_);
lean_dec(v_ns_1500_);
lean_dec_ref(v_env_1498_);
v___x_1520_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1517_);
v___x_1521_ = lean_box(0);
v___x_1522_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1504_, v___x_1520_, v___x_1521_);
return v___x_1522_;
}
}
v___jp_1524_:
{
lean_object* v___x_1526_; 
lean_inc(v_id_1511_);
lean_inc_ref(v_env_1498_);
v___x_1526_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1498_, v_opts_1499_, v_id_1511_);
if (lean_obj_tag(v___x_1526_) == 1)
{
lean_object* v_val_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_val_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_val_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1523_);
v___x_1529_ = l_List_appendTR___redArg(v___x_1528_, v___y_1525_);
v___y_1513_ = v___x_1529_;
goto v___jp_1512_;
}
else
{
lean_dec(v___x_1526_);
lean_dec(v___x_1523_);
v___y_1513_ = v___y_1525_;
goto v___jp_1512_;
}
}
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_projs_1504_);
lean_dec(v_id_1503_);
lean_dec(v_openDecls_1501_);
lean_dec(v_ns_1500_);
lean_dec_ref(v_env_1498_);
v___x_1540_ = lean_box(0);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1541_, lean_object* v_opts_1542_, lean_object* v_ns_1543_, lean_object* v_openDecls_1544_, lean_object* v_extractionResult_1545_, lean_object* v_id_1546_, lean_object* v_projs_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1541_, v_opts_1542_, v_ns_1543_, v_openDecls_1544_, v_extractionResult_1545_, v_id_1546_, v_projs_1547_);
lean_dec_ref(v_extractionResult_1545_);
lean_dec_ref(v_opts_1542_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1549_, lean_object* v_opts_1550_, lean_object* v_ns_1551_, lean_object* v_openDecls_1552_, lean_object* v_id_1553_){
_start:
{
lean_object* v_extractionResult_1554_; lean_object* v_name_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_extractionResult_1554_ = l_Lean_extractMacroScopes(v_id_1553_);
v_name_1555_ = lean_ctor_get(v_extractionResult_1554_, 0);
lean_inc(v_name_1555_);
v___x_1556_ = lean_box(0);
v___x_1557_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1549_, v_opts_1550_, v_ns_1551_, v_openDecls_1552_, v_extractionResult_1554_, v_name_1555_, v___x_1556_);
lean_dec_ref(v_extractionResult_1554_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1558_, lean_object* v_opts_1559_, lean_object* v_ns_1560_, lean_object* v_openDecls_1561_, lean_object* v_id_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_ResolveName_resolveGlobalName(v_env_1558_, v_opts_1559_, v_ns_1560_, v_openDecls_1561_, v_id_1562_);
lean_dec_ref(v_opts_1559_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_panic_fn(v___x_1565_, v_msg_1564_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1570_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1571_ = lean_unsigned_to_nat(9u);
v___x_1572_ = lean_unsigned_to_nat(230u);
v___x_1573_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1574_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1575_ = l_mkPanicMessageWithDecl(v___x_1574_, v___x_1573_, v___x_1572_, v___x_1571_, v___x_1570_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1576_, lean_object* v_n_1577_, lean_object* v_ns_1578_){
_start:
{
switch(lean_obj_tag(v_ns_1578_))
{
case 1:
{
lean_object* v_pre_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_pre_1579_ = lean_ctor_get(v_ns_1578_, 0);
lean_inc(v_pre_1579_);
lean_inc(v_n_1577_);
v___x_1580_ = l_Lean_Name_append(v_ns_1578_, v_n_1577_);
lean_inc_ref(v_env_1576_);
v___x_1581_ = l_Lean_Environment_isNamespace(v_env_1576_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_dec(v___x_1580_);
v_ns_1578_ = v_pre_1579_;
goto _start;
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_pre_1579_);
lean_dec(v_n_1577_);
lean_dec_ref(v_env_1576_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1580_);
return v___x_1583_;
}
}
case 0:
{
lean_object* v___x_1584_; lean_object* v_n_1585_; uint8_t v___x_1586_; 
v___x_1584_ = l_Lean_rootNamespace;
v_n_1585_ = l_Lean_Name_replacePrefix(v_n_1577_, v___x_1584_, v_ns_1578_);
v___x_1586_ = l_Lean_Environment_isNamespace(v_env_1576_, v_n_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_dec(v_n_1585_);
v___x_1587_ = lean_box(0);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_n_1585_);
return v___x_1588_;
}
}
default: 
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_ns_1578_);
lean_dec(v_n_1577_);
lean_dec_ref(v_env_1576_);
v___x_1589_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1590_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1589_);
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1591_, lean_object* v_n_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 0)
{
lean_object* v___x_1594_; 
lean_dec(v_n_1592_);
lean_dec_ref(v_env_1591_);
v___x_1594_ = lean_box(0);
return v___x_1594_;
}
else
{
lean_object* v_head_1595_; 
v_head_1595_ = lean_ctor_get(v_x_1593_, 0);
if (lean_obj_tag(v_head_1595_) == 0)
{
lean_object* v_tail_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1613_; 
lean_inc_ref(v_head_1595_);
v_tail_1596_ = lean_ctor_get(v_x_1593_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_x_1593_, 0);
lean_dec(v_unused_1614_);
v___x_1598_ = v_x_1593_;
v_isShared_1599_ = v_isSharedCheck_1613_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_tail_1596_);
lean_dec(v_x_1593_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1613_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_ns_1600_; lean_object* v_except_1601_; lean_object* v___x_1602_; uint8_t v___y_1604_; uint8_t v___x_1610_; 
v_ns_1600_ = lean_ctor_get(v_head_1595_, 0);
lean_inc(v_ns_1600_);
v_except_1601_ = lean_ctor_get(v_head_1595_, 1);
lean_inc(v_except_1601_);
lean_dec_ref(v_head_1595_);
lean_inc(v_n_1592_);
v___x_1602_ = l_Lean_Name_append(v_ns_1600_, v_n_1592_);
lean_inc_ref(v_env_1591_);
v___x_1610_ = l_Lean_Environment_isNamespace(v_env_1591_, v___x_1602_);
if (v___x_1610_ == 0)
{
lean_dec(v_except_1601_);
v___y_1604_ = v___x_1610_;
goto v___jp_1603_;
}
else
{
uint8_t v___x_1611_; 
v___x_1611_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1592_, v_except_1601_);
lean_dec(v_except_1601_);
if (v___x_1611_ == 0)
{
v___y_1604_ = v___x_1610_;
goto v___jp_1603_;
}
else
{
lean_dec(v___x_1602_);
lean_del_object(v___x_1598_);
v_x_1593_ = v_tail_1596_;
goto _start;
}
}
v___jp_1603_:
{
if (v___y_1604_ == 0)
{
lean_dec(v___x_1602_);
lean_del_object(v___x_1598_);
v_x_1593_ = v_tail_1596_;
goto _start;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1591_, v_n_1592_, v_tail_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1606_);
lean_ctor_set(v___x_1598_, 0, v___x_1602_);
v___x_1608_ = v___x_1598_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_object* v_tail_1615_; 
v_tail_1615_ = lean_ctor_get(v_x_1593_, 1);
lean_inc(v_tail_1615_);
lean_dec_ref(v_x_1593_);
v_x_1593_ = v_tail_1615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1617_, lean_object* v_ns_1618_, lean_object* v_openDecls_1619_, lean_object* v_id_1620_){
_start:
{
lean_object* v___x_1621_; 
lean_inc(v_id_1620_);
lean_inc_ref(v_env_1617_);
v___x_1621_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1617_, v_id_1620_, v_ns_1618_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1617_, v_id_1620_, v_openDecls_1619_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_val_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref(v___x_1621_);
v___x_1624_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1617_, v_id_1620_, v_openDecls_1619_);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_val_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1626_, lean_object* v_inst_1627_){
_start:
{
lean_object* v_getCurrNamespace_1628_; lean_object* v_getOpenDecls_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1638_; 
v_getCurrNamespace_1628_ = lean_ctor_get(v_inst_1627_, 0);
v_getOpenDecls_1629_ = lean_ctor_get(v_inst_1627_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_inst_1627_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1631_ = v_inst_1627_;
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_getOpenDecls_1629_);
lean_inc(v_getCurrNamespace_1628_);
lean_dec(v_inst_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_inc(v_inst_1626_);
v___x_1633_ = lean_apply_2(v_inst_1626_, lean_box(0), v_getCurrNamespace_1628_);
v___x_1634_ = lean_apply_2(v_inst_1626_, lean_box(0), v_getOpenDecls_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___x_1634_);
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1639_, lean_object* v_n_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1641_, v_inst_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1650_, lean_object* v_toApplicative_1651_, lean_object* v_id_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, uint8_t v_____do__lift_1657_){
_start:
{
uint8_t v_isExporting_1662_; 
v_isExporting_1662_ = lean_ctor_get_uint8(v_____do__lift_1650_, sizeof(void*)*8);
if (v_isExporting_1662_ == 0)
{
lean_dec(v_inst_1656_);
lean_dec(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_inst_1653_);
lean_dec(v_id_1652_);
goto v___jp_1658_;
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Lean_isPrivateName(v_id_1652_);
if (v___x_1663_ == 0)
{
lean_dec(v_inst_1656_);
lean_dec(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_inst_1653_);
lean_dec(v_id_1652_);
goto v___jp_1658_;
}
else
{
if (v_____do__lift_1657_ == 0)
{
lean_dec(v_inst_1656_);
lean_dec(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_inst_1653_);
lean_dec(v_id_1652_);
goto v___jp_1658_;
}
else
{
lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v_toApplicative_1651_);
v___x_1664_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1665_ = 0;
v___x_1666_ = l_Lean_MessageData_ofConstName(v_id_1652_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_logWarning___redArg(v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v___x_1669_);
return v___x_1670_;
}
}
}
v___jp_1658_:
{
lean_object* v_toPure_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_toPure_1659_ = lean_ctor_get(v_toApplicative_1651_, 1);
lean_inc(v_toPure_1659_);
lean_dec_ref(v_toApplicative_1651_);
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_apply_2(v_toPure_1659_, lean_box(0), v___x_1660_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1671_, lean_object* v_toApplicative_1672_, lean_object* v_id_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_____do__lift_1678_){
_start:
{
uint8_t v_____do__lift_230__boxed_1679_; lean_object* v_res_1680_; 
v_____do__lift_230__boxed_1679_ = lean_unbox(v_____do__lift_1678_);
v_res_1680_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1671_, v_toApplicative_1672_, v_id_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_____do__lift_230__boxed_1679_);
lean_dec_ref(v_____do__lift_1671_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toApplicative_1681_, lean_object* v_id_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v___x_1687_, lean_object* v_toBind_1688_, lean_object* v_____do__lift_1689_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_inc(v_inst_1686_);
lean_inc_ref(v_inst_1683_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1690_, 0, v_____do__lift_1689_);
lean_closure_set(v___f_1690_, 1, v_toApplicative_1681_);
lean_closure_set(v___f_1690_, 2, v_id_1682_);
lean_closure_set(v___f_1690_, 3, v_inst_1683_);
lean_closure_set(v___f_1690_, 4, v_inst_1684_);
lean_closure_set(v___f_1690_, 5, v_inst_1685_);
lean_closure_set(v___f_1690_, 6, v_inst_1686_);
v___x_1691_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1692_ = l_Lean_Option_getM___redArg(v_inst_1683_, v_inst_1686_, v___x_1687_, v___x_1691_);
v___x_1693_ = lean_apply_4(v_toBind_1688_, lean_box(0), lean_box(0), v___x_1692_, v___f_1690_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_id_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v_toApplicative_1701_; lean_object* v_toBind_1702_; lean_object* v_getEnv_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; 
v___x_1700_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1701_ = lean_ctor_get(v_inst_1694_, 0);
lean_inc_ref(v_toApplicative_1701_);
v_toBind_1702_ = lean_ctor_get(v_inst_1694_, 1);
lean_inc(v_toBind_1702_);
v_getEnv_1703_ = lean_ctor_get(v_inst_1695_, 0);
lean_inc(v_getEnv_1703_);
lean_dec_ref(v_inst_1695_);
lean_inc(v_toBind_1702_);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1704_, 0, v_toApplicative_1701_);
lean_closure_set(v___f_1704_, 1, v_id_1699_);
lean_closure_set(v___f_1704_, 2, v_inst_1694_);
lean_closure_set(v___f_1704_, 3, v_inst_1697_);
lean_closure_set(v___f_1704_, 4, v_inst_1698_);
lean_closure_set(v___f_1704_, 5, v_inst_1696_);
lean_closure_set(v___f_1704_, 6, v___x_1700_);
lean_closure_set(v___f_1704_, 7, v_toBind_1702_);
v___x_1705_ = lean_apply_4(v_toBind_1702_, lean_box(0), lean_box(0), v_getEnv_1703_, v___f_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_id_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1707_, v_inst_1708_, v_inst_1709_, v_inst_1710_, v_inst_1711_, v_id_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1714_, lean_object* v_n_1715_, lean_object* v_toApplicative_1716_, uint8_t v___y_1717_, uint8_t v___x_1718_, lean_object* v_____r_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1714_, v_n_1715_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_toPure_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_toPure_1721_ = lean_ctor_get(v_toApplicative_1716_, 1);
lean_inc(v_toPure_1721_);
lean_dec_ref(v_toApplicative_1716_);
v___x_1722_ = lean_box(v___y_1717_);
v___x_1723_ = lean_apply_2(v_toPure_1721_, lean_box(0), v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v_val_1724_; lean_object* v_toPure_1725_; lean_object* v___x_1726_; uint8_t v_isModule_1727_; 
v_val_1724_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_val_1724_);
lean_dec_ref(v___x_1720_);
v_toPure_1725_ = lean_ctor_get(v_toApplicative_1716_, 1);
lean_inc(v_toPure_1725_);
lean_dec_ref(v_toApplicative_1716_);
v___x_1726_ = l_Lean_Environment_header(v_env_1714_);
v_isModule_1727_ = lean_ctor_get_uint8(v___x_1726_, sizeof(void*)*7 + 4);
if (v_isModule_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v___x_1726_);
lean_dec(v_val_1724_);
v___x_1728_ = lean_box(v___x_1718_);
v___x_1729_ = lean_apply_2(v_toPure_1725_, lean_box(0), v___x_1728_);
return v___x_1729_;
}
else
{
lean_object* v_modules_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v_modules_1730_ = lean_ctor_get(v___x_1726_, 3);
lean_inc_ref(v_modules_1730_);
lean_dec_ref(v___x_1726_);
v___x_1731_ = lean_array_get_size(v_modules_1730_);
v___x_1732_ = lean_nat_dec_lt(v_val_1724_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec_ref(v_modules_1730_);
lean_dec(v_val_1724_);
v___x_1733_ = lean_box(v_isModule_1727_);
v___x_1734_ = lean_apply_2(v_toPure_1725_, lean_box(0), v___x_1733_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v_toImport_1736_; uint8_t v_importAll_1737_; 
v___x_1735_ = lean_array_fget(v_modules_1730_, v_val_1724_);
lean_dec(v_val_1724_);
lean_dec_ref(v_modules_1730_);
v_toImport_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc_ref(v_toImport_1736_);
lean_dec(v___x_1735_);
v_importAll_1737_ = lean_ctor_get_uint8(v_toImport_1736_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1736_);
if (v_importAll_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_box(v_isModule_1727_);
v___x_1739_ = lean_apply_2(v_toPure_1725_, lean_box(0), v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_box(v___y_1717_);
v___x_1741_ = lean_apply_2(v_toPure_1725_, lean_box(0), v___x_1740_);
return v___x_1741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1742_, lean_object* v_n_1743_, lean_object* v_toApplicative_1744_, lean_object* v___y_1745_, lean_object* v___x_1746_, lean_object* v_____r_1747_){
_start:
{
uint8_t v___y_758__boxed_1748_; uint8_t v___x_759__boxed_1749_; lean_object* v_res_1750_; 
v___y_758__boxed_1748_ = lean_unbox(v___y_1745_);
v___x_759__boxed_1749_ = lean_unbox(v___x_1746_);
v_res_1750_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1742_, v_n_1743_, v_toApplicative_1744_, v___y_758__boxed_1748_, v___x_759__boxed_1749_, v_____r_1747_);
lean_dec(v_n_1743_);
lean_dec_ref(v_env_1742_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1751_, lean_object* v_n_1752_, lean_object* v_toApplicative_1753_, uint8_t v___x_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_toBind_1760_, uint8_t v___x_1761_, uint8_t v_____do__lift_1762_){
_start:
{
uint8_t v___y_1764_; uint8_t v_isExporting_1770_; 
v_isExporting_1770_ = lean_ctor_get_uint8(v_env_1751_, sizeof(void*)*8);
if (v_isExporting_1770_ == 0)
{
v___y_1764_ = v_isExporting_1770_;
goto v___jp_1763_;
}
else
{
if (v_____do__lift_1762_ == 0)
{
lean_object* v_toPure_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_toBind_1760_);
lean_dec(v_inst_1759_);
lean_dec_ref(v_inst_1758_);
lean_dec(v_inst_1757_);
lean_dec_ref(v_inst_1756_);
lean_dec_ref(v_inst_1755_);
lean_dec(v_n_1752_);
lean_dec_ref(v_env_1751_);
v_toPure_1771_ = lean_ctor_get(v_toApplicative_1753_, 1);
lean_inc(v_toPure_1771_);
lean_dec_ref(v_toApplicative_1753_);
v___x_1772_ = lean_box(v___x_1754_);
v___x_1773_ = lean_apply_2(v_toPure_1771_, lean_box(0), v___x_1772_);
return v___x_1773_;
}
else
{
v___y_1764_ = v___x_1761_;
goto v___jp_1763_;
}
}
v___jp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___f_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1765_ = lean_box(v___y_1764_);
v___x_1766_ = lean_box(v___x_1754_);
lean_inc(v_n_1752_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1767_, 0, v_env_1751_);
lean_closure_set(v___f_1767_, 1, v_n_1752_);
lean_closure_set(v___f_1767_, 2, v_toApplicative_1753_);
lean_closure_set(v___f_1767_, 3, v___x_1765_);
lean_closure_set(v___f_1767_, 4, v___x_1766_);
v___x_1768_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1755_, v_inst_1756_, v_inst_1757_, v_inst_1758_, v_inst_1759_, v_n_1752_);
v___x_1769_ = lean_apply_4(v_toBind_1760_, lean_box(0), lean_box(0), v___x_1768_, v___f_1767_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1774_, lean_object* v_n_1775_, lean_object* v_toApplicative_1776_, lean_object* v___x_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_toBind_1783_, lean_object* v___x_1784_, lean_object* v_____do__lift_1785_){
_start:
{
uint8_t v___x_799__boxed_1786_; uint8_t v___x_805__boxed_1787_; uint8_t v_____do__lift_806__boxed_1788_; lean_object* v_res_1789_; 
v___x_799__boxed_1786_ = lean_unbox(v___x_1777_);
v___x_805__boxed_1787_ = lean_unbox(v___x_1784_);
v_____do__lift_806__boxed_1788_ = lean_unbox(v_____do__lift_1785_);
v_res_1789_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1774_, v_n_1775_, v_toApplicative_1776_, v___x_799__boxed_1786_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_inst_1781_, v_inst_1782_, v_toBind_1783_, v___x_805__boxed_1787_, v_____do__lift_806__boxed_1788_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1790_, lean_object* v_toApplicative_1791_, uint8_t v___x_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_toBind_1798_, uint8_t v___x_1799_, lean_object* v_env_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1801_ = lean_box(v___x_1792_);
v___x_1802_ = lean_box(v___x_1799_);
lean_inc(v_toBind_1798_);
lean_inc(v_inst_1795_);
lean_inc_ref(v_inst_1793_);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1803_, 0, v_env_1800_);
lean_closure_set(v___f_1803_, 1, v_n_1790_);
lean_closure_set(v___f_1803_, 2, v_toApplicative_1791_);
lean_closure_set(v___f_1803_, 3, v___x_1801_);
lean_closure_set(v___f_1803_, 4, v_inst_1793_);
lean_closure_set(v___f_1803_, 5, v_inst_1794_);
lean_closure_set(v___f_1803_, 6, v_inst_1795_);
lean_closure_set(v___f_1803_, 7, v_inst_1796_);
lean_closure_set(v___f_1803_, 8, v_inst_1797_);
lean_closure_set(v___f_1803_, 9, v_toBind_1798_);
lean_closure_set(v___f_1803_, 10, v___x_1802_);
v___x_1804_ = l_Lean_KVMap_instValueBool;
v___x_1805_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1806_ = l_Lean_Option_getM___redArg(v_inst_1793_, v_inst_1795_, v___x_1804_, v___x_1805_);
v___x_1807_ = lean_apply_4(v_toBind_1798_, lean_box(0), lean_box(0), v___x_1806_, v___f_1803_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1808_, lean_object* v_toApplicative_1809_, lean_object* v___x_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_toBind_1816_, lean_object* v___x_1817_, lean_object* v_env_1818_){
_start:
{
uint8_t v___x_841__boxed_1819_; uint8_t v___x_847__boxed_1820_; lean_object* v_res_1821_; 
v___x_841__boxed_1819_ = lean_unbox(v___x_1810_);
v___x_847__boxed_1820_ = lean_unbox(v___x_1817_);
v_res_1821_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1808_, v_toApplicative_1809_, v___x_841__boxed_1819_, v_inst_1811_, v_inst_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v_toBind_1816_, v___x_847__boxed_1820_, v_env_1818_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_n_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Lean_isPrivateName(v_n_1827_);
if (v___x_1828_ == 0)
{
lean_object* v_toApplicative_1829_; lean_object* v_toPure_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v_n_1827_);
lean_dec(v_inst_1826_);
lean_dec_ref(v_inst_1825_);
lean_dec(v_inst_1823_);
lean_dec_ref(v_inst_1822_);
v_toApplicative_1829_ = lean_ctor_get(v_inst_1824_, 0);
lean_inc_ref(v_toApplicative_1829_);
lean_dec_ref(v_inst_1824_);
v_toPure_1830_ = lean_ctor_get(v_toApplicative_1829_, 1);
lean_inc(v_toPure_1830_);
lean_dec_ref(v_toApplicative_1829_);
v___x_1831_ = lean_box(v___x_1828_);
v___x_1832_ = lean_apply_2(v_toPure_1830_, lean_box(0), v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v_toApplicative_1833_; lean_object* v_toBind_1834_; lean_object* v_getEnv_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; 
v_toApplicative_1833_ = lean_ctor_get(v_inst_1824_, 0);
lean_inc_ref(v_toApplicative_1833_);
v_toBind_1834_ = lean_ctor_get(v_inst_1824_, 1);
lean_inc(v_toBind_1834_);
v_getEnv_1835_ = lean_ctor_get(v_inst_1825_, 0);
lean_inc(v_getEnv_1835_);
v___x_1836_ = 0;
v___x_1837_ = lean_box(v___x_1828_);
v___x_1838_ = lean_box(v___x_1836_);
lean_inc(v_toBind_1834_);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1839_, 0, v_n_1827_);
lean_closure_set(v___f_1839_, 1, v_toApplicative_1833_);
lean_closure_set(v___f_1839_, 2, v___x_1837_);
lean_closure_set(v___f_1839_, 3, v_inst_1824_);
lean_closure_set(v___f_1839_, 4, v_inst_1825_);
lean_closure_set(v___f_1839_, 5, v_inst_1826_);
lean_closure_set(v___f_1839_, 6, v_inst_1822_);
lean_closure_set(v___f_1839_, 7, v_inst_1823_);
lean_closure_set(v___f_1839_, 8, v_toBind_1834_);
lean_closure_set(v___f_1839_, 9, v___x_1838_);
v___x_1840_ = lean_apply_4(v_toBind_1834_, lean_box(0), lean_box(0), v_getEnv_1835_, v___f_1839_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_n_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_inst_1846_, v_n_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1849_){
_start:
{
lean_object* v_fst_1850_; uint8_t v___x_1851_; 
v_fst_1850_ = lean_ctor_get(v_x_1849_, 0);
v___x_1851_ = l_Lean_isPrivateName(v_fst_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1852_);
lean_dec_ref(v_x_1852_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1855_, lean_object* v_res_1856_, lean_object* v_____r_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_apply_2(v_toPure_1855_, lean_box(0), v_res_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1859_, lean_object* v_toPure_1860_, lean_object* v_res_1861_, lean_object* v___f_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_toBind_1868_, lean_object* v___f_1869_, lean_object* v_____do__lift_1870_){
_start:
{
if (v_enableLog_1859_ == 0)
{
lean_object* v___x_1871_; 
lean_dec(v___f_1869_);
lean_dec(v_toBind_1868_);
lean_dec(v_inst_1867_);
lean_dec_ref(v_inst_1866_);
lean_dec(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
lean_dec_ref(v_inst_1863_);
lean_dec_ref(v___f_1862_);
v___x_1871_ = lean_apply_2(v_toPure_1860_, lean_box(0), v_res_1861_);
return v___x_1871_;
}
else
{
uint8_t v_isExporting_1872_; 
v_isExporting_1872_ = lean_ctor_get_uint8(v_____do__lift_1870_, sizeof(void*)*8);
if (v_isExporting_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec(v___f_1869_);
lean_dec(v_toBind_1868_);
lean_dec(v_inst_1867_);
lean_dec_ref(v_inst_1866_);
lean_dec(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
lean_dec_ref(v_inst_1863_);
lean_dec_ref(v___f_1862_);
v___x_1873_ = lean_apply_2(v_toPure_1860_, lean_box(0), v_res_1861_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; 
lean_inc(v_res_1861_);
v___x_1874_ = l_List_find_x3f___redArg(v___f_1862_, v_res_1861_);
if (lean_obj_tag(v___x_1874_) == 1)
{
lean_object* v_val_1875_; lean_object* v_fst_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_res_1861_);
lean_dec(v_toPure_1860_);
v_val_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref(v___x_1874_);
v_fst_1876_ = lean_ctor_get(v_val_1875_, 0);
lean_inc(v_fst_1876_);
lean_dec(v_val_1875_);
v___x_1877_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1863_, v_inst_1864_, v_inst_1865_, v_inst_1866_, v_inst_1867_, v_fst_1876_);
v___x_1878_ = lean_apply_4(v_toBind_1868_, lean_box(0), lean_box(0), v___x_1877_, v___f_1869_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; 
lean_dec(v___x_1874_);
lean_dec(v___f_1869_);
lean_dec(v_toBind_1868_);
lean_dec(v_inst_1867_);
lean_dec_ref(v_inst_1866_);
lean_dec(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
lean_dec_ref(v_inst_1863_);
v___x_1879_ = lean_apply_2(v_toPure_1860_, lean_box(0), v_res_1861_);
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1880_, lean_object* v_toPure_1881_, lean_object* v_res_1882_, lean_object* v___f_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_toBind_1889_, lean_object* v___f_1890_, lean_object* v_____do__lift_1891_){
_start:
{
uint8_t v_enableLog_boxed_1892_; lean_object* v_res_1893_; 
v_enableLog_boxed_1892_ = lean_unbox(v_enableLog_1880_);
v_res_1893_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1892_, v_toPure_1881_, v_res_1882_, v___f_1883_, v_inst_1884_, v_inst_1885_, v_inst_1886_, v_inst_1887_, v_inst_1888_, v_toBind_1889_, v___f_1890_, v_____do__lift_1891_);
lean_dec_ref(v_____do__lift_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1894_, lean_object* v_____do__lift_1895_, lean_object* v_____do__lift_1896_, lean_object* v_id_1897_, lean_object* v_toPure_1898_, uint8_t v_enableLog_1899_, lean_object* v___f_1900_, lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_toBind_1906_, lean_object* v_getEnv_1907_, lean_object* v_____do__lift_1908_){
_start:
{
lean_object* v_res_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
v_res_1909_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1894_, v_____do__lift_1895_, v_____do__lift_1896_, v_____do__lift_1908_, v_id_1897_);
lean_inc(v_res_1909_);
lean_inc(v_toPure_1898_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1910_, 0, v_toPure_1898_);
lean_closure_set(v___f_1910_, 1, v_res_1909_);
v___x_1911_ = lean_box(v_enableLog_1899_);
lean_inc(v_toBind_1906_);
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1912_, 0, v___x_1911_);
lean_closure_set(v___f_1912_, 1, v_toPure_1898_);
lean_closure_set(v___f_1912_, 2, v_res_1909_);
lean_closure_set(v___f_1912_, 3, v___f_1900_);
lean_closure_set(v___f_1912_, 4, v_inst_1901_);
lean_closure_set(v___f_1912_, 5, v_inst_1902_);
lean_closure_set(v___f_1912_, 6, v_inst_1903_);
lean_closure_set(v___f_1912_, 7, v_inst_1904_);
lean_closure_set(v___f_1912_, 8, v_inst_1905_);
lean_closure_set(v___f_1912_, 9, v_toBind_1906_);
lean_closure_set(v___f_1912_, 10, v___f_1910_);
v___x_1913_ = lean_apply_4(v_toBind_1906_, lean_box(0), lean_box(0), v_getEnv_1907_, v___f_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1914_, lean_object* v_____do__lift_1915_, lean_object* v_____do__lift_1916_, lean_object* v_id_1917_, lean_object* v_toPure_1918_, lean_object* v_enableLog_1919_, lean_object* v___f_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_toBind_1926_, lean_object* v_getEnv_1927_, lean_object* v_____do__lift_1928_){
_start:
{
uint8_t v_enableLog_boxed_1929_; lean_object* v_res_1930_; 
v_enableLog_boxed_1929_ = lean_unbox(v_enableLog_1919_);
v_res_1930_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1914_, v_____do__lift_1915_, v_____do__lift_1916_, v_id_1917_, v_toPure_1918_, v_enableLog_boxed_1929_, v___f_1920_, v_inst_1921_, v_inst_1922_, v_inst_1923_, v_inst_1924_, v_inst_1925_, v_toBind_1926_, v_getEnv_1927_, v_____do__lift_1928_);
lean_dec_ref(v_____do__lift_1915_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1931_, lean_object* v_____do__lift_1932_, lean_object* v_id_1933_, lean_object* v_toPure_1934_, uint8_t v_enableLog_1935_, lean_object* v___f_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_toBind_1942_, lean_object* v_getEnv_1943_, lean_object* v_getOpenDecls_1944_, lean_object* v_____do__lift_1945_){
_start:
{
lean_object* v___x_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_box(v_enableLog_1935_);
lean_inc(v_toBind_1942_);
v___f_1947_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1947_, 0, v_____do__lift_1931_);
lean_closure_set(v___f_1947_, 1, v_____do__lift_1932_);
lean_closure_set(v___f_1947_, 2, v_____do__lift_1945_);
lean_closure_set(v___f_1947_, 3, v_id_1933_);
lean_closure_set(v___f_1947_, 4, v_toPure_1934_);
lean_closure_set(v___f_1947_, 5, v___x_1946_);
lean_closure_set(v___f_1947_, 6, v___f_1936_);
lean_closure_set(v___f_1947_, 7, v_inst_1937_);
lean_closure_set(v___f_1947_, 8, v_inst_1938_);
lean_closure_set(v___f_1947_, 9, v_inst_1939_);
lean_closure_set(v___f_1947_, 10, v_inst_1940_);
lean_closure_set(v___f_1947_, 11, v_inst_1941_);
lean_closure_set(v___f_1947_, 12, v_toBind_1942_);
lean_closure_set(v___f_1947_, 13, v_getEnv_1943_);
v___x_1948_ = lean_apply_4(v_toBind_1942_, lean_box(0), lean_box(0), v_getOpenDecls_1944_, v___f_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1949_, lean_object* v_____do__lift_1950_, lean_object* v_id_1951_, lean_object* v_toPure_1952_, lean_object* v_enableLog_1953_, lean_object* v___f_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_toBind_1960_, lean_object* v_getEnv_1961_, lean_object* v_getOpenDecls_1962_, lean_object* v_____do__lift_1963_){
_start:
{
uint8_t v_enableLog_boxed_1964_; lean_object* v_res_1965_; 
v_enableLog_boxed_1964_ = lean_unbox(v_enableLog_1953_);
v_res_1965_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1949_, v_____do__lift_1950_, v_id_1951_, v_toPure_1952_, v_enableLog_boxed_1964_, v___f_1954_, v_inst_1955_, v_inst_1956_, v_inst_1957_, v_inst_1958_, v_inst_1959_, v_toBind_1960_, v_getEnv_1961_, v_getOpenDecls_1962_, v_____do__lift_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1966_, lean_object* v_____do__lift_1967_, lean_object* v_id_1968_, lean_object* v_toPure_1969_, uint8_t v_enableLog_1970_, lean_object* v___f_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_toBind_1977_, lean_object* v_getEnv_1978_, lean_object* v_____do__lift_1979_){
_start:
{
lean_object* v_getCurrNamespace_1980_; lean_object* v_getOpenDecls_1981_; lean_object* v___x_1982_; lean_object* v___f_1983_; lean_object* v___x_1984_; 
v_getCurrNamespace_1980_ = lean_ctor_get(v_inst_1966_, 0);
lean_inc(v_getCurrNamespace_1980_);
v_getOpenDecls_1981_ = lean_ctor_get(v_inst_1966_, 1);
lean_inc(v_getOpenDecls_1981_);
lean_dec_ref(v_inst_1966_);
v___x_1982_ = lean_box(v_enableLog_1970_);
lean_inc(v_toBind_1977_);
v___f_1983_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1983_, 0, v_____do__lift_1967_);
lean_closure_set(v___f_1983_, 1, v_____do__lift_1979_);
lean_closure_set(v___f_1983_, 2, v_id_1968_);
lean_closure_set(v___f_1983_, 3, v_toPure_1969_);
lean_closure_set(v___f_1983_, 4, v___x_1982_);
lean_closure_set(v___f_1983_, 5, v___f_1971_);
lean_closure_set(v___f_1983_, 6, v_inst_1972_);
lean_closure_set(v___f_1983_, 7, v_inst_1973_);
lean_closure_set(v___f_1983_, 8, v_inst_1974_);
lean_closure_set(v___f_1983_, 9, v_inst_1975_);
lean_closure_set(v___f_1983_, 10, v_inst_1976_);
lean_closure_set(v___f_1983_, 11, v_toBind_1977_);
lean_closure_set(v___f_1983_, 12, v_getEnv_1978_);
lean_closure_set(v___f_1983_, 13, v_getOpenDecls_1981_);
v___x_1984_ = lean_apply_4(v_toBind_1977_, lean_box(0), lean_box(0), v_getCurrNamespace_1980_, v___f_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1985_, lean_object* v_____do__lift_1986_, lean_object* v_id_1987_, lean_object* v_toPure_1988_, lean_object* v_enableLog_1989_, lean_object* v___f_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_toBind_1996_, lean_object* v_getEnv_1997_, lean_object* v_____do__lift_1998_){
_start:
{
uint8_t v_enableLog_boxed_1999_; lean_object* v_res_2000_; 
v_enableLog_boxed_1999_ = lean_unbox(v_enableLog_1989_);
v_res_2000_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1985_, v_____do__lift_1986_, v_id_1987_, v_toPure_1988_, v_enableLog_boxed_1999_, v___f_1990_, v_inst_1991_, v_inst_1992_, v_inst_1993_, v_inst_1994_, v_inst_1995_, v_toBind_1996_, v_getEnv_1997_, v_____do__lift_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_2001_, lean_object* v_id_2002_, lean_object* v_toPure_2003_, uint8_t v_enableLog_2004_, lean_object* v___f_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_toBind_2011_, lean_object* v_getEnv_2012_, lean_object* v_____do__lift_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(v_enableLog_2004_);
lean_inc(v_toBind_2011_);
lean_inc(v_inst_2008_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_2015_, 0, v_inst_2001_);
lean_closure_set(v___f_2015_, 1, v_____do__lift_2013_);
lean_closure_set(v___f_2015_, 2, v_id_2002_);
lean_closure_set(v___f_2015_, 3, v_toPure_2003_);
lean_closure_set(v___f_2015_, 4, v___x_2014_);
lean_closure_set(v___f_2015_, 5, v___f_2005_);
lean_closure_set(v___f_2015_, 6, v_inst_2006_);
lean_closure_set(v___f_2015_, 7, v_inst_2007_);
lean_closure_set(v___f_2015_, 8, v_inst_2008_);
lean_closure_set(v___f_2015_, 9, v_inst_2009_);
lean_closure_set(v___f_2015_, 10, v_inst_2010_);
lean_closure_set(v___f_2015_, 11, v_toBind_2011_);
lean_closure_set(v___f_2015_, 12, v_getEnv_2012_);
v___x_2016_ = lean_apply_4(v_toBind_2011_, lean_box(0), lean_box(0), v_inst_2008_, v___f_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_2017_, lean_object* v_id_2018_, lean_object* v_toPure_2019_, lean_object* v_enableLog_2020_, lean_object* v___f_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_toBind_2027_, lean_object* v_getEnv_2028_, lean_object* v_____do__lift_2029_){
_start:
{
uint8_t v_enableLog_boxed_2030_; lean_object* v_res_2031_; 
v_enableLog_boxed_2030_ = lean_unbox(v_enableLog_2020_);
v_res_2031_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2017_, v_id_2018_, v_toPure_2019_, v_enableLog_boxed_2030_, v___f_2021_, v_inst_2022_, v_inst_2023_, v_inst_2024_, v_inst_2025_, v_inst_2026_, v_toBind_2027_, v_getEnv_2028_, v_____do__lift_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_id_2039_, uint8_t v_enableLog_2040_){
_start:
{
lean_object* v_toApplicative_2041_; lean_object* v_toBind_2042_; lean_object* v_getEnv_2043_; lean_object* v_toPure_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; lean_object* v___f_2047_; lean_object* v___x_2048_; 
v_toApplicative_2041_ = lean_ctor_get(v_inst_2033_, 0);
v_toBind_2042_ = lean_ctor_get(v_inst_2033_, 1);
lean_inc(v_toBind_2042_);
v_getEnv_2043_ = lean_ctor_get(v_inst_2035_, 0);
lean_inc(v_getEnv_2043_);
v_toPure_2044_ = lean_ctor_get(v_toApplicative_2041_, 1);
lean_inc(v_toPure_2044_);
v___f_2045_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2046_ = lean_box(v_enableLog_2040_);
lean_inc(v_getEnv_2043_);
lean_inc(v_toBind_2042_);
v___f_2047_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2047_, 0, v_inst_2034_);
lean_closure_set(v___f_2047_, 1, v_id_2039_);
lean_closure_set(v___f_2047_, 2, v_toPure_2044_);
lean_closure_set(v___f_2047_, 3, v___x_2046_);
lean_closure_set(v___f_2047_, 4, v___f_2045_);
lean_closure_set(v___f_2047_, 5, v_inst_2033_);
lean_closure_set(v___f_2047_, 6, v_inst_2035_);
lean_closure_set(v___f_2047_, 7, v_inst_2036_);
lean_closure_set(v___f_2047_, 8, v_inst_2037_);
lean_closure_set(v___f_2047_, 9, v_inst_2038_);
lean_closure_set(v___f_2047_, 10, v_toBind_2042_);
lean_closure_set(v___f_2047_, 11, v_getEnv_2043_);
v___x_2048_ = lean_apply_4(v_toBind_2042_, lean_box(0), lean_box(0), v_getEnv_2043_, v___f_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_id_2055_, lean_object* v_enableLog_2056_){
_start:
{
uint8_t v_enableLog_boxed_2057_; lean_object* v_res_2058_; 
v_enableLog_boxed_2057_ = lean_unbox(v_enableLog_2056_);
v_res_2058_ = l_Lean_resolveGlobalName___redArg(v_inst_2049_, v_inst_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v_id_2055_, v_enableLog_boxed_2057_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_id_2066_, uint8_t v_enableLog_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_resolveGlobalName___redArg(v_inst_2060_, v_inst_2061_, v_inst_2062_, v_inst_2063_, v_inst_2064_, v_inst_2065_, v_id_2066_, v_enableLog_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_id_2076_, lean_object* v_enableLog_2077_){
_start:
{
uint8_t v_enableLog_boxed_2078_; lean_object* v_res_2079_; 
v_enableLog_boxed_2078_ = lean_unbox(v_enableLog_2077_);
v_res_2079_ = l_Lean_resolveGlobalName(v_m_2069_, v_inst_2070_, v_inst_2071_, v_inst_2072_, v_inst_2073_, v_inst_2074_, v_inst_2075_, v_id_2076_, v_enableLog_boxed_2078_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2080_, lean_object* v_nss_2081_, lean_object* v_____r_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_apply_2(v_toPure_2080_, lean_box(0), v_nss_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2086_, lean_object* v_____do__lift_2087_, lean_object* v_id_2088_, uint8_t v_allowEmpty_2089_, lean_object* v_toPure_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_toBind_2093_, lean_object* v_____do__lift_2094_){
_start:
{
lean_object* v_nss_2095_; 
lean_inc(v_id_2088_);
v_nss_2095_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2086_, v_____do__lift_2087_, v_____do__lift_2094_, v_id_2088_);
if (v_allowEmpty_2089_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = l_List_isEmpty___redArg(v_nss_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec(v_toBind_2093_);
lean_dec_ref(v_inst_2092_);
lean_dec_ref(v_inst_2091_);
lean_dec(v_id_2088_);
v___x_2097_ = lean_apply_2(v_toPure_2090_, lean_box(0), v_nss_2095_);
return v___x_2097_;
}
else
{
lean_object* v___f_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2098_, 0, v_toPure_2090_);
lean_closure_set(v___f_2098_, 1, v_nss_2095_);
v___x_2099_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2100_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2088_, v___x_2096_);
v___x_2101_ = lean_string_append(v___x_2099_, v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2103_ = lean_string_append(v___x_2101_, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
v___x_2105_ = l_Lean_MessageData_ofFormat(v___x_2104_);
v___x_2106_ = l_Lean_throwError___redArg(v_inst_2091_, v_inst_2092_, v___x_2105_);
v___x_2107_ = lean_apply_4(v_toBind_2093_, lean_box(0), lean_box(0), v___x_2106_, v___f_2098_);
return v___x_2107_;
}
}
else
{
lean_object* v___x_2108_; 
lean_dec(v_toBind_2093_);
lean_dec_ref(v_inst_2092_);
lean_dec_ref(v_inst_2091_);
lean_dec(v_id_2088_);
v___x_2108_ = lean_apply_2(v_toPure_2090_, lean_box(0), v_nss_2095_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2109_, lean_object* v_____do__lift_2110_, lean_object* v_id_2111_, lean_object* v_allowEmpty_2112_, lean_object* v_toPure_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_toBind_2116_, lean_object* v_____do__lift_2117_){
_start:
{
uint8_t v_allowEmpty_boxed_2118_; lean_object* v_res_2119_; 
v_allowEmpty_boxed_2118_ = lean_unbox(v_allowEmpty_2112_);
v_res_2119_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2109_, v_____do__lift_2110_, v_id_2111_, v_allowEmpty_boxed_2118_, v_toPure_2113_, v_inst_2114_, v_inst_2115_, v_toBind_2116_, v_____do__lift_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2120_, lean_object* v_id_2121_, uint8_t v_allowEmpty_2122_, lean_object* v_toPure_2123_, lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_toBind_2126_, lean_object* v_getOpenDecls_2127_, lean_object* v_____do__lift_2128_){
_start:
{
lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(v_allowEmpty_2122_);
lean_inc(v_toBind_2126_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2130_, 0, v_____do__lift_2120_);
lean_closure_set(v___f_2130_, 1, v_____do__lift_2128_);
lean_closure_set(v___f_2130_, 2, v_id_2121_);
lean_closure_set(v___f_2130_, 3, v___x_2129_);
lean_closure_set(v___f_2130_, 4, v_toPure_2123_);
lean_closure_set(v___f_2130_, 5, v_inst_2124_);
lean_closure_set(v___f_2130_, 6, v_inst_2125_);
lean_closure_set(v___f_2130_, 7, v_toBind_2126_);
v___x_2131_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v_getOpenDecls_2127_, v___f_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2132_, lean_object* v_id_2133_, lean_object* v_allowEmpty_2134_, lean_object* v_toPure_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_toBind_2138_, lean_object* v_getOpenDecls_2139_, lean_object* v_____do__lift_2140_){
_start:
{
uint8_t v_allowEmpty_boxed_2141_; lean_object* v_res_2142_; 
v_allowEmpty_boxed_2141_ = lean_unbox(v_allowEmpty_2134_);
v_res_2142_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2132_, v_id_2133_, v_allowEmpty_boxed_2141_, v_toPure_2135_, v_inst_2136_, v_inst_2137_, v_toBind_2138_, v_getOpenDecls_2139_, v_____do__lift_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2143_, lean_object* v_id_2144_, uint8_t v_allowEmpty_2145_, lean_object* v_toPure_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_toBind_2149_, lean_object* v_____do__lift_2150_){
_start:
{
lean_object* v_getCurrNamespace_2151_; lean_object* v_getOpenDecls_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___x_2155_; 
v_getCurrNamespace_2151_ = lean_ctor_get(v_inst_2143_, 0);
lean_inc(v_getCurrNamespace_2151_);
v_getOpenDecls_2152_ = lean_ctor_get(v_inst_2143_, 1);
lean_inc(v_getOpenDecls_2152_);
lean_dec_ref(v_inst_2143_);
v___x_2153_ = lean_box(v_allowEmpty_2145_);
lean_inc(v_toBind_2149_);
v___f_2154_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2154_, 0, v_____do__lift_2150_);
lean_closure_set(v___f_2154_, 1, v_id_2144_);
lean_closure_set(v___f_2154_, 2, v___x_2153_);
lean_closure_set(v___f_2154_, 3, v_toPure_2146_);
lean_closure_set(v___f_2154_, 4, v_inst_2147_);
lean_closure_set(v___f_2154_, 5, v_inst_2148_);
lean_closure_set(v___f_2154_, 6, v_toBind_2149_);
lean_closure_set(v___f_2154_, 7, v_getOpenDecls_2152_);
v___x_2155_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v_getCurrNamespace_2151_, v___f_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2156_, lean_object* v_id_2157_, lean_object* v_allowEmpty_2158_, lean_object* v_toPure_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_toBind_2162_, lean_object* v_____do__lift_2163_){
_start:
{
uint8_t v_allowEmpty_boxed_2164_; lean_object* v_res_2165_; 
v_allowEmpty_boxed_2164_ = lean_unbox(v_allowEmpty_2158_);
v_res_2165_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2156_, v_id_2157_, v_allowEmpty_boxed_2164_, v_toPure_2159_, v_inst_2160_, v_inst_2161_, v_toBind_2162_, v_____do__lift_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_inst_2169_, lean_object* v_id_2170_, uint8_t v_allowEmpty_2171_){
_start:
{
lean_object* v_toApplicative_2172_; lean_object* v_toBind_2173_; lean_object* v_getEnv_2174_; lean_object* v_toPure_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; 
v_toApplicative_2172_ = lean_ctor_get(v_inst_2166_, 0);
v_toBind_2173_ = lean_ctor_get(v_inst_2166_, 1);
lean_inc(v_toBind_2173_);
v_getEnv_2174_ = lean_ctor_get(v_inst_2168_, 0);
lean_inc(v_getEnv_2174_);
lean_dec_ref(v_inst_2168_);
v_toPure_2175_ = lean_ctor_get(v_toApplicative_2172_, 1);
lean_inc(v_toPure_2175_);
v___x_2176_ = lean_box(v_allowEmpty_2171_);
lean_inc(v_toBind_2173_);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2177_, 0, v_inst_2167_);
lean_closure_set(v___f_2177_, 1, v_id_2170_);
lean_closure_set(v___f_2177_, 2, v___x_2176_);
lean_closure_set(v___f_2177_, 3, v_toPure_2175_);
lean_closure_set(v___f_2177_, 4, v_inst_2166_);
lean_closure_set(v___f_2177_, 5, v_inst_2169_);
lean_closure_set(v___f_2177_, 6, v_toBind_2173_);
v___x_2178_ = lean_apply_4(v_toBind_2173_, lean_box(0), lean_box(0), v_getEnv_2174_, v___f_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_id_2183_, lean_object* v_allowEmpty_2184_){
_start:
{
uint8_t v_allowEmpty_boxed_2185_; lean_object* v_res_2186_; 
v_allowEmpty_boxed_2185_ = lean_unbox(v_allowEmpty_2184_);
v_res_2186_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2179_, v_inst_2180_, v_inst_2181_, v_inst_2182_, v_id_2183_, v_allowEmpty_boxed_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_, lean_object* v_id_2192_, uint8_t v_allowEmpty_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2188_, v_inst_2189_, v_inst_2190_, v_inst_2191_, v_id_2192_, v_allowEmpty_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2195_, lean_object* v_inst_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_id_2200_, lean_object* v_allowEmpty_2201_){
_start:
{
uint8_t v_allowEmpty_boxed_2202_; lean_object* v_res_2203_; 
v_allowEmpty_boxed_2202_ = lean_unbox(v_allowEmpty_2201_);
v_res_2203_ = l_Lean_resolveNamespaceCore(v_m_2195_, v_inst_2196_, v_inst_2197_, v_inst_2198_, v_inst_2199_, v_id_2200_, v_allowEmpty_boxed_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v_ns_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_ns_2205_ = lean_ctor_get(v_x_2204_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_2204_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v_x_2204_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_ns_2205_);
lean_dec(v_x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set_tag(v___x_2207_, 1);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_ns_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v___x_2213_; 
lean_dec_ref(v_x_2204_);
v___x_2213_ = lean_box(0);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2214_, lean_object* v_withRef_2215_, lean_object* v___x_2216_, lean_object* v_oldRef_2217_){
_start:
{
lean_object* v_ref_2218_; lean_object* v___x_2219_; 
v_ref_2218_ = l_Lean_replaceRef(v_x_2214_, v_oldRef_2217_);
v___x_2219_ = lean_apply_3(v_withRef_2215_, lean_box(0), v_ref_2218_, v___x_2216_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2220_, lean_object* v_withRef_2221_, lean_object* v___x_2222_, lean_object* v_oldRef_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2220_, v_withRef_2221_, v___x_2222_, v_oldRef_2223_);
lean_dec(v_oldRef_2223_);
lean_dec(v_x_2220_);
return v_res_2224_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2232_ = l_Lean_MessageData_ofFormat(v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_x_2237_){
_start:
{
if (lean_obj_tag(v_x_2237_) == 3)
{
lean_object* v_val_2238_; lean_object* v_preresolved_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; lean_object* v_pre_2242_; uint8_t v___x_2243_; 
v_val_2238_ = lean_ctor_get(v_x_2237_, 2);
v_preresolved_2239_ = lean_ctor_get(v_x_2237_, 3);
v___f_2240_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2241_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2239_);
v_pre_2242_ = l_List_filterMapTR_go___redArg(v___f_2240_, v_preresolved_2239_, v___x_2241_);
v___x_2243_ = l_List_isEmpty___redArg(v_pre_2242_);
if (v___x_2243_ == 0)
{
lean_object* v_toApplicative_2244_; lean_object* v_toPure_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v_x_2237_);
lean_dec_ref(v_inst_2236_);
lean_dec_ref(v_inst_2235_);
lean_dec_ref(v_inst_2234_);
v_toApplicative_2244_ = lean_ctor_get(v_inst_2233_, 0);
lean_inc_ref(v_toApplicative_2244_);
lean_dec_ref(v_inst_2233_);
v_toPure_2245_ = lean_ctor_get(v_toApplicative_2244_, 1);
lean_inc(v_toPure_2245_);
lean_dec_ref(v_toApplicative_2244_);
v___x_2246_ = lean_apply_2(v_toPure_2245_, lean_box(0), v_pre_2242_);
return v___x_2246_;
}
else
{
lean_object* v_toMonadRef_2247_; lean_object* v_toBind_2248_; lean_object* v_getRef_2249_; lean_object* v_withRef_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; 
lean_dec(v_pre_2242_);
v_toMonadRef_2247_ = lean_ctor_get(v_inst_2236_, 1);
v_toBind_2248_ = lean_ctor_get(v_inst_2233_, 1);
lean_inc(v_toBind_2248_);
v_getRef_2249_ = lean_ctor_get(v_toMonadRef_2247_, 0);
lean_inc(v_getRef_2249_);
v_withRef_2250_ = lean_ctor_get(v_toMonadRef_2247_, 1);
lean_inc(v_withRef_2250_);
v___x_2251_ = 0;
lean_inc(v_val_2238_);
v___x_2252_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2233_, v_inst_2234_, v_inst_2235_, v_inst_2236_, v_val_2238_, v___x_2251_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2253_, 0, v_x_2237_);
lean_closure_set(v___f_2253_, 1, v_withRef_2250_);
lean_closure_set(v___f_2253_, 2, v___x_2252_);
v___x_2254_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v_getRef_2249_, v___f_2253_);
return v___x_2254_;
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v_inst_2235_);
lean_dec_ref(v_inst_2234_);
v___x_2255_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2256_ = l_Lean_throwErrorAt___redArg(v_inst_2233_, v_inst_2236_, v_x_2237_, v___x_2255_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_x_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_resolveNamespace___redArg(v_inst_2258_, v_inst_2259_, v_inst_2260_, v_inst_2261_, v_x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2266_, lean_object* v___f_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_toPure_2270_, lean_object* v_____do__lift_2271_){
_start:
{
if (lean_obj_tag(v_____do__lift_2271_) == 1)
{
lean_object* v_tail_2287_; 
v_tail_2287_ = lean_ctor_get(v_____do__lift_2271_, 1);
if (lean_obj_tag(v_tail_2287_) == 0)
{
lean_object* v_head_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_inst_2269_);
lean_dec_ref(v_inst_2268_);
lean_dec_ref(v___f_2267_);
v_head_2288_ = lean_ctor_get(v_____do__lift_2271_, 0);
lean_inc(v_head_2288_);
lean_dec_ref(v_____do__lift_2271_);
v___x_2289_ = lean_apply_2(v_toPure_2270_, lean_box(0), v_head_2288_);
return v___x_2289_;
}
else
{
lean_dec(v_toPure_2270_);
goto v___jp_2272_;
}
}
else
{
lean_dec(v_toPure_2270_);
goto v___jp_2272_;
}
v___jp_2272_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2273_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2274_ = l_Lean_TSyntax_getId(v_id_2266_);
v___x_2275_ = 1;
v___x_2276_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2274_, v___x_2275_);
v___x_2277_ = lean_string_append(v___x_2273_, v___x_2276_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
v___x_2280_ = l_List_toString___redArg(v___f_2267_, v_____do__lift_2271_);
v___x_2281_ = lean_string_append(v___x_2279_, v___x_2280_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2283_ = lean_string_append(v___x_2281_, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
v___x_2285_ = l_Lean_MessageData_ofFormat(v___x_2284_);
v___x_2286_ = l_Lean_throwError___redArg(v_inst_2268_, v_inst_2269_, v___x_2285_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2290_, lean_object* v___f_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_toPure_2294_, lean_object* v_____do__lift_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2290_, v___f_2291_, v_inst_2292_, v_inst_2293_, v_toPure_2294_, v_____do__lift_2295_);
lean_dec(v_id_2290_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_id_2302_){
_start:
{
lean_object* v_toApplicative_2303_; lean_object* v_toBind_2304_; lean_object* v_toPure_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v_toApplicative_2303_ = lean_ctor_get(v_inst_2298_, 0);
v_toBind_2304_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc(v_toBind_2304_);
v_toPure_2305_ = lean_ctor_get(v_toApplicative_2303_, 1);
lean_inc(v_toPure_2305_);
v___f_2306_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2302_);
lean_inc_ref(v_inst_2301_);
lean_inc_ref(v_inst_2298_);
v___x_2307_ = l_Lean_resolveNamespace___redArg(v_inst_2298_, v_inst_2299_, v_inst_2300_, v_inst_2301_, v_id_2302_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2308_, 0, v_id_2302_);
lean_closure_set(v___f_2308_, 1, v___f_2306_);
lean_closure_set(v___f_2308_, 2, v_inst_2298_);
lean_closure_set(v___f_2308_, 3, v_inst_2301_);
lean_closure_set(v___f_2308_, 4, v_toPure_2305_);
v___x_2309_ = lean_apply_4(v_toBind_2304_, lean_box(0), lean_box(0), v___x_2307_, v___f_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_inst_2314_, lean_object* v_id_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2311_, v_inst_2312_, v_inst_2313_, v_inst_2314_, v_id_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2317_){
_start:
{
lean_object* v_snd_2318_; uint8_t v___x_2319_; 
v_snd_2318_ = lean_ctor_get(v_x_2317_, 1);
v___x_2319_ = l_List_isEmpty___redArg(v_snd_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2320_){
_start:
{
uint8_t v_res_2321_; lean_object* v_r_2322_; 
v_res_2321_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2320_);
lean_dec_ref(v_x_2320_);
v_r_2322_ = lean_box(v_res_2321_);
return v_r_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2323_){
_start:
{
lean_object* v_fst_2324_; 
v_fst_2324_ = lean_ctor_get(v_x_2323_, 0);
lean_inc(v_fst_2324_);
return v_fst_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2325_);
lean_dec_ref(v_x_2325_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2327_, lean_object* v_cs_2328_, lean_object* v_toPure_2329_, lean_object* v_____r_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_box(0);
v___x_2332_ = l_List_mapTR_loop___redArg(v___f_2327_, v_cs_2328_, v___x_2331_);
v___x_2333_ = lean_apply_2(v_toPure_2329_, lean_box(0), v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2334_, lean_object* v_____r_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_apply_1(v___f_2334_, v_____r_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_n_2340_, lean_object* v_toBind_2341_, lean_object* v___f_2342_, lean_object* v_____do__lift_2343_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_____do__lift_2343_, v_n_2340_);
v___x_2345_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v___x_2344_, v___f_2342_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_n_2351_, lean_object* v_cs_2352_){
_start:
{
lean_object* v_toApplicative_2353_; lean_object* v_toBind_2354_; lean_object* v_toPure_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v___x_2358_; lean_object* v_cs_2359_; lean_object* v___f_2360_; uint8_t v___x_2361_; 
v_toApplicative_2353_ = lean_ctor_get(v_inst_2348_, 0);
v_toBind_2354_ = lean_ctor_get(v_inst_2348_, 1);
lean_inc(v_toBind_2354_);
v_toPure_2355_ = lean_ctor_get(v_toApplicative_2353_, 1);
v___f_2356_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2357_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2358_ = lean_box(0);
v_cs_2359_ = l_List_filterTR_loop___redArg(v___f_2356_, v_cs_2352_, v___x_2358_);
lean_inc(v_toPure_2355_);
lean_inc(v_cs_2359_);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2360_, 0, v___f_2357_);
lean_closure_set(v___f_2360_, 1, v_cs_2359_);
lean_closure_set(v___f_2360_, 2, v_toPure_2355_);
v___x_2361_ = l_List_isEmpty___redArg(v_cs_2359_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_inc(v_toPure_2355_);
lean_dec_ref(v___f_2360_);
lean_dec(v_toBind_2354_);
lean_dec(v_n_2351_);
lean_dec_ref(v_inst_2350_);
lean_dec_ref(v_inst_2349_);
lean_dec_ref(v_inst_2348_);
v___x_2362_ = lean_box(0);
v___x_2363_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2357_, v_cs_2359_, v_toPure_2355_, v___x_2362_);
return v___x_2363_;
}
else
{
lean_object* v_toMonadRef_2364_; lean_object* v_getRef_2365_; lean_object* v___f_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; 
lean_dec(v_cs_2359_);
v_toMonadRef_2364_ = lean_ctor_get(v_inst_2350_, 1);
v_getRef_2365_ = lean_ctor_get(v_toMonadRef_2364_, 0);
lean_inc(v_getRef_2365_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2366_, 0, v___f_2360_);
lean_inc(v_toBind_2354_);
v___f_2367_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2367_, 0, v_inst_2348_);
lean_closure_set(v___f_2367_, 1, v_inst_2349_);
lean_closure_set(v___f_2367_, 2, v_inst_2350_);
lean_closure_set(v___f_2367_, 3, v_n_2351_);
lean_closure_set(v___f_2367_, 4, v_toBind_2354_);
lean_closure_set(v___f_2367_, 5, v___f_2366_);
v___x_2368_ = lean_apply_4(v_toBind_2354_, lean_box(0), lean_box(0), v_getRef_2365_, v___f_2367_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_n_2373_, lean_object* v_cs_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_filterFieldList___redArg(v_inst_2370_, v_inst_2371_, v_inst_2372_, v_n_2373_, v_cs_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_n_2379_, lean_object* v_cs_2380_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_filterFieldList___redArg(v_inst_2376_, v_inst_2377_, v_inst_2378_, v_n_2379_, v_cs_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_inst_2387_, lean_object* v_inst_2388_, lean_object* v_n_2389_){
_start:
{
lean_object* v_toBind_2390_; lean_object* v___f_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_toBind_2390_ = lean_ctor_get(v_inst_2382_, 1);
lean_inc(v_toBind_2390_);
lean_inc(v_n_2389_);
lean_inc_ref(v_inst_2384_);
lean_inc_ref(v_inst_2382_);
v___f_2391_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2391_, 0, v_inst_2382_);
lean_closure_set(v___f_2391_, 1, v_inst_2384_);
lean_closure_set(v___f_2391_, 2, v_inst_2388_);
lean_closure_set(v___f_2391_, 3, v_n_2389_);
v___x_2392_ = 1;
v___x_2393_ = l_Lean_resolveGlobalName___redArg(v_inst_2382_, v_inst_2383_, v_inst_2384_, v_inst_2385_, v_inst_2386_, v_inst_2387_, v_n_2389_, v___x_2392_);
v___x_2394_ = lean_apply_4(v_toBind_2390_, lean_box(0), lean_box(0), v___x_2393_, v___f_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_n_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2396_, v_inst_2397_, v_inst_2398_, v_inst_2399_, v_inst_2400_, v_inst_2401_, v_inst_2402_, v_n_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2405_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_box(0);
v___x_2407_ = l_Lean_mkConst(v_declName_2405_, v___x_2406_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2414_ = l_Lean_stringToMessageData(v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_n_2418_, lean_object* v_cs_2419_){
_start:
{
lean_object* v_toApplicative_2420_; lean_object* v_toPure_2421_; lean_object* v___f_2422_; 
v_toApplicative_2420_ = lean_ctor_get(v_inst_2416_, 0);
v_toPure_2421_ = lean_ctor_get(v_toApplicative_2420_, 1);
v___f_2422_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2419_) == 1)
{
lean_object* v_tail_2436_; 
v_tail_2436_ = lean_ctor_get(v_cs_2419_, 1);
if (lean_obj_tag(v_tail_2436_) == 0)
{
lean_object* v_head_2437_; lean_object* v___x_2438_; 
lean_inc(v_toPure_2421_);
lean_dec(v_n_2418_);
lean_dec_ref(v_inst_2417_);
lean_dec_ref(v_inst_2416_);
v_head_2437_ = lean_ctor_get(v_cs_2419_, 0);
lean_inc(v_head_2437_);
lean_dec_ref(v_cs_2419_);
v___x_2438_ = lean_apply_2(v_toPure_2421_, lean_box(0), v_head_2437_);
return v___x_2438_;
}
else
{
goto v___jp_2423_;
}
}
else
{
goto v___jp_2423_;
}
v___jp_2423_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2424_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2425_ = l_Lean_MessageData_ofName(v_n_2418_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_box(0);
v___x_2430_ = l_List_mapTR_loop___redArg(v___f_2422_, v_cs_2419_, v___x_2429_);
v___x_2431_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2432_ = l_List_mapTR_loop___redArg(v___x_2431_, v___x_2430_, v___x_2429_);
v___x_2433_ = l_Lean_MessageData_ofList(v___x_2432_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2428_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = l_Lean_throwError___redArg(v_inst_2416_, v_inst_2417_, v___x_2434_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_n_2442_, lean_object* v_cs_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_ensureNoOverload___redArg(v_inst_2440_, v_inst_2441_, v_n_2442_, v_cs_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_n_2447_, lean_object* v_____do__lift_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_ensureNoOverload___redArg(v_inst_2445_, v_inst_2446_, v_n_2447_, v_____do__lift_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_n_2457_){
_start:
{
lean_object* v_toBind_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_toBind_2458_ = lean_ctor_get(v_inst_2450_, 1);
lean_inc(v_toBind_2458_);
lean_inc(v_n_2457_);
lean_inc_ref(v_inst_2456_);
lean_inc_ref(v_inst_2450_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2459_, 0, v_inst_2450_);
lean_closure_set(v___f_2459_, 1, v_inst_2456_);
lean_closure_set(v___f_2459_, 2, v_n_2457_);
v___x_2460_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2450_, v_inst_2451_, v_inst_2452_, v_inst_2453_, v_inst_2454_, v_inst_2455_, v_inst_2456_, v_n_2457_);
v___x_2461_ = lean_apply_4(v_toBind_2458_, lean_box(0), lean_box(0), v___x_2460_, v___f_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_n_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2463_, v_inst_2464_, v_inst_2465_, v_inst_2466_, v_inst_2467_, v_inst_2468_, v_inst_2469_, v_n_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2472_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 1)
{
lean_object* v_fields_2473_; 
v_fields_2473_ = lean_ctor_get(v_x_2472_, 1);
if (lean_obj_tag(v_fields_2473_) == 0)
{
lean_object* v_n_2474_; lean_object* v___x_2475_; 
v_n_2474_ = lean_ctor_get(v_x_2472_, 0);
lean_inc(v_n_2474_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_n_2474_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
}
else
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_box(0);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2478_);
lean_dec_ref(v_x_2478_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2480_, lean_object* v_withRef_2481_, lean_object* v___x_2482_, lean_object* v_oldRef_2483_){
_start:
{
lean_object* v_ref_2484_; lean_object* v___x_2485_; 
v_ref_2484_ = l_Lean_replaceRef(v_stx_2480_, v_oldRef_2483_);
v___x_2485_ = lean_apply_3(v_withRef_2481_, lean_box(0), v_ref_2484_, v___x_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2486_, lean_object* v_withRef_2487_, lean_object* v___x_2488_, lean_object* v_oldRef_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2486_, v_withRef_2487_, v___x_2488_, v_oldRef_2489_);
lean_dec(v_oldRef_2489_);
lean_dec(v_stx_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_stx_2494_, lean_object* v_k_2495_){
_start:
{
if (lean_obj_tag(v_stx_2494_) == 3)
{
lean_object* v_val_2496_; lean_object* v_preresolved_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; lean_object* v_pre_2500_; uint8_t v___x_2501_; 
v_val_2496_ = lean_ctor_get(v_stx_2494_, 2);
v_preresolved_2497_ = lean_ctor_get(v_stx_2494_, 3);
v___f_2498_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2499_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2497_);
v_pre_2500_ = l_List_filterMapTR_go___redArg(v___f_2498_, v_preresolved_2497_, v___x_2499_);
v___x_2501_ = l_List_isEmpty___redArg(v_pre_2500_);
if (v___x_2501_ == 0)
{
lean_object* v_toApplicative_2502_; lean_object* v_toPure_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v_stx_2494_);
lean_dec(v_k_2495_);
lean_dec_ref(v_inst_2493_);
v_toApplicative_2502_ = lean_ctor_get(v_inst_2492_, 0);
lean_inc_ref(v_toApplicative_2502_);
lean_dec_ref(v_inst_2492_);
v_toPure_2503_ = lean_ctor_get(v_toApplicative_2502_, 1);
lean_inc(v_toPure_2503_);
lean_dec_ref(v_toApplicative_2502_);
v___x_2504_ = lean_apply_2(v_toPure_2503_, lean_box(0), v_pre_2500_);
return v___x_2504_;
}
else
{
lean_object* v_toMonadRef_2505_; lean_object* v_toBind_2506_; lean_object* v_getRef_2507_; lean_object* v_withRef_2508_; lean_object* v___x_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; 
lean_dec(v_pre_2500_);
v_toMonadRef_2505_ = lean_ctor_get(v_inst_2493_, 1);
lean_inc_ref(v_toMonadRef_2505_);
lean_dec_ref(v_inst_2493_);
v_toBind_2506_ = lean_ctor_get(v_inst_2492_, 1);
lean_inc(v_toBind_2506_);
lean_dec_ref(v_inst_2492_);
v_getRef_2507_ = lean_ctor_get(v_toMonadRef_2505_, 0);
lean_inc(v_getRef_2507_);
v_withRef_2508_ = lean_ctor_get(v_toMonadRef_2505_, 1);
lean_inc(v_withRef_2508_);
lean_dec_ref(v_toMonadRef_2505_);
lean_inc(v_val_2496_);
v___x_2509_ = lean_apply_1(v_k_2495_, v_val_2496_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2510_, 0, v_stx_2494_);
lean_closure_set(v___f_2510_, 1, v_withRef_2508_);
lean_closure_set(v___f_2510_, 2, v___x_2509_);
v___x_2511_ = lean_apply_4(v_toBind_2506_, lean_box(0), lean_box(0), v_getRef_2507_, v___f_2510_);
return v___x_2511_;
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec(v_k_2495_);
v___x_2512_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2513_ = l_Lean_throwErrorAt___redArg(v_inst_2492_, v_inst_2493_, v_stx_2494_, v___x_2512_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_stx_2517_, lean_object* v_k_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2515_, v_inst_2516_, v_stx_2517_, v_k_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_inst_2526_, lean_object* v_stx_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_inc_ref(v_inst_2526_);
lean_inc_ref(v_inst_2520_);
v___x_2528_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2528_, 0, lean_box(0));
lean_closure_set(v___x_2528_, 1, v_inst_2520_);
lean_closure_set(v___x_2528_, 2, v_inst_2521_);
lean_closure_set(v___x_2528_, 3, v_inst_2522_);
lean_closure_set(v___x_2528_, 4, v_inst_2523_);
lean_closure_set(v___x_2528_, 5, v_inst_2524_);
lean_closure_set(v___x_2528_, 6, v_inst_2525_);
lean_closure_set(v___x_2528_, 7, v_inst_2526_);
v___x_2529_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2520_, v_inst_2526_, v_stx_2527_, v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_inst_2537_, lean_object* v_stx_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_resolveGlobalConst___redArg(v_inst_2531_, v_inst_2532_, v_inst_2533_, v_inst_2534_, v_inst_2535_, v_inst_2536_, v_inst_2537_, v_stx_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2541_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2542_ = lean_unsigned_to_nat(11u);
v___x_2543_ = lean_unsigned_to_nat(429u);
v___x_2544_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2545_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2546_ = l_mkPanicMessageWithDecl(v___x_2545_, v___x_2544_, v___x_2543_, v___x_2542_, v___x_2541_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_id_2552_, lean_object* v_cs_2553_){
_start:
{
if (lean_obj_tag(v_cs_2553_) == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_id_2552_);
lean_dec_ref(v_inst_2551_);
v___x_2554_ = lean_box(0);
v___x_2555_ = l_instInhabitedOfMonad___redArg(v_inst_2550_, v___x_2554_);
v___x_2556_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2557_ = l_panic___redArg(v___x_2555_, v___x_2556_);
return v___x_2557_;
}
else
{
lean_object* v_tail_2558_; 
v_tail_2558_ = lean_ctor_get(v_cs_2553_, 1);
if (lean_obj_tag(v_tail_2558_) == 0)
{
lean_object* v_toApplicative_2559_; lean_object* v_toPure_2560_; lean_object* v_head_2561_; lean_object* v___x_2562_; 
v_toApplicative_2559_ = lean_ctor_get(v_inst_2550_, 0);
lean_inc_ref(v_toApplicative_2559_);
lean_dec(v_id_2552_);
lean_dec_ref(v_inst_2551_);
lean_dec_ref(v_inst_2550_);
v_toPure_2560_ = lean_ctor_get(v_toApplicative_2559_, 1);
lean_inc(v_toPure_2560_);
lean_dec_ref(v_toApplicative_2559_);
v_head_2561_ = lean_ctor_get(v_cs_2553_, 0);
lean_inc(v_head_2561_);
lean_dec_ref(v_cs_2553_);
v___x_2562_ = lean_apply_2(v_toPure_2560_, lean_box(0), v_head_2561_);
return v___x_2562_;
}
else
{
lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___f_2563_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2564_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2565_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2566_ = lean_box(0);
v___x_2567_ = 0;
lean_inc(v_id_2552_);
v___x_2568_ = l_Lean_Syntax_formatStx(v_id_2552_, v___x_2566_, v___x_2567_);
v___x_2569_ = l_Std_Format_defWidth;
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = l_Std_Format_pretty(v___x_2568_, v___x_2569_, v___x_2570_, v___x_2570_);
v___x_2572_ = lean_string_append(v___x_2565_, v___x_2571_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2574_ = lean_string_append(v___x_2572_, v___x_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = l_List_mapTR_loop___redArg(v___f_2563_, v_cs_2553_, v___x_2575_);
v___x_2577_ = l_List_toString___redArg(v___x_2564_, v___x_2576_);
v___x_2578_ = lean_string_append(v___x_2574_, v___x_2577_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
v___x_2580_ = l_Lean_MessageData_ofFormat(v___x_2579_);
v___x_2581_ = l_Lean_throwErrorAt___redArg(v_inst_2550_, v_inst_2551_, v_id_2552_, v___x_2580_);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_id_2585_, lean_object* v_cs_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2583_, v_inst_2584_, v_id_2585_, v_cs_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_id_2590_, lean_object* v_____do__lift_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2588_, v_inst_2589_, v_id_2590_, v_____do__lift_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_id_2600_){
_start:
{
lean_object* v_toBind_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_toBind_2601_ = lean_ctor_get(v_inst_2593_, 1);
lean_inc(v_toBind_2601_);
lean_inc(v_id_2600_);
lean_inc_ref(v_inst_2599_);
lean_inc_ref(v_inst_2593_);
v___f_2602_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2602_, 0, v_inst_2593_);
lean_closure_set(v___f_2602_, 1, v_inst_2599_);
lean_closure_set(v___f_2602_, 2, v_id_2600_);
v___x_2603_ = l_Lean_resolveGlobalConst___redArg(v_inst_2593_, v_inst_2594_, v_inst_2595_, v_inst_2596_, v_inst_2597_, v_inst_2598_, v_inst_2599_, v_id_2600_);
v___x_2604_ = lean_apply_4(v_toBind_2601_, lean_box(0), lean_box(0), v___x_2603_, v___f_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_id_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2606_, v_inst_2607_, v_inst_2608_, v_inst_2609_, v_inst_2610_, v_inst_2611_, v_inst_2612_, v_id_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2615_, lean_object* v___f_2616_, uint8_t v_globalDeclFoundNext_2617_, uint8_t v_globalDeclFound_2618_, lean_object* v_r_2619_){
_start:
{
lean_object* v___x_2620_; lean_object* v_r_2621_; uint8_t v___x_2622_; 
v___x_2620_ = lean_box(0);
v_r_2621_ = l_List_filterTR_loop___redArg(v___f_2615_, v_r_2619_, v___x_2620_);
v___x_2622_ = l_List_isEmpty___redArg(v_r_2621_);
lean_dec(v_r_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_box(0);
v___x_2624_ = lean_box(v_globalDeclFoundNext_2617_);
v___x_2625_ = lean_apply_2(v___f_2616_, v___x_2623_, v___x_2624_);
return v___x_2625_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_box(v_globalDeclFound_2618_);
v___x_2628_ = lean_apply_2(v___f_2616_, v___x_2626_, v___x_2627_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2629_, lean_object* v___f_2630_, lean_object* v_globalDeclFoundNext_2631_, lean_object* v_globalDeclFound_2632_, lean_object* v_r_2633_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2634_; uint8_t v_globalDeclFound_boxed_2635_; lean_object* v_res_2636_; 
v_globalDeclFoundNext_boxed_2634_ = lean_unbox(v_globalDeclFoundNext_2631_);
v_globalDeclFound_boxed_2635_ = lean_unbox(v_globalDeclFound_2632_);
v_res_2636_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2629_, v___f_2630_, v_globalDeclFoundNext_boxed_2634_, v_globalDeclFound_boxed_2635_, v_r_2633_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2637_, lean_object* v_projs_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_inst_2644_, lean_object* v_view_2645_, lean_object* v_findLocalDecl_x3f_2646_, lean_object* v_pre_2647_, lean_object* v_____r_2648_, lean_object* v_globalDeclFoundNext_2649_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2650_; lean_object* v_res_2651_; 
v_globalDeclFoundNext_boxed_2650_ = lean_unbox(v_globalDeclFoundNext_2649_);
v_res_2651_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2637_, v_projs_2638_, v_inst_2639_, v_inst_2640_, v_inst_2641_, v_inst_2642_, v_inst_2643_, v_inst_2644_, v_view_2645_, v_findLocalDecl_x3f_2646_, v_pre_2647_, v_____r_2648_, v_globalDeclFoundNext_boxed_2650_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_view_2658_, lean_object* v_findLocalDecl_x3f_2659_, lean_object* v_n_2660_, lean_object* v_projs_2661_, uint8_t v_globalDeclFound_2662_){
_start:
{
lean_object* v_toApplicative_2663_; lean_object* v_imported_2664_; lean_object* v_ctx_2665_; lean_object* v_scopes_2666_; lean_object* v_toBind_2667_; lean_object* v_toPure_2668_; lean_object* v___f_2669_; lean_object* v_givenNameView_2670_; uint8_t v___y_2672_; 
v_toApplicative_2663_ = lean_ctor_get(v_inst_2652_, 0);
v_imported_2664_ = lean_ctor_get(v_view_2658_, 1);
v_ctx_2665_ = lean_ctor_get(v_view_2658_, 2);
v_scopes_2666_ = lean_ctor_get(v_view_2658_, 3);
v_toBind_2667_ = lean_ctor_get(v_inst_2652_, 1);
v_toPure_2668_ = lean_ctor_get(v_toApplicative_2663_, 1);
v___f_2669_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2666_);
lean_inc(v_ctx_2665_);
lean_inc(v_imported_2664_);
lean_inc(v_n_2660_);
v_givenNameView_2670_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2670_, 0, v_n_2660_);
lean_ctor_set(v_givenNameView_2670_, 1, v_imported_2664_);
lean_ctor_set(v_givenNameView_2670_, 2, v_ctx_2665_);
lean_ctor_set(v_givenNameView_2670_, 3, v_scopes_2666_);
if (v_globalDeclFound_2662_ == 0)
{
v___y_2672_ = v_globalDeclFound_2662_;
goto v___jp_2671_;
}
else
{
uint8_t v___x_2708_; 
v___x_2708_ = l_List_isEmpty___redArg(v_projs_2661_);
if (v___x_2708_ == 0)
{
v___y_2672_ = v_globalDeclFound_2662_;
goto v___jp_2671_;
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = 0;
v___y_2672_ = v___x_2709_;
goto v___jp_2671_;
}
}
v___jp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_box(v___y_2672_);
lean_inc_ref(v_findLocalDecl_x3f_2659_);
lean_inc_ref(v_givenNameView_2670_);
v___x_2674_ = lean_apply_2(v_findLocalDecl_x3f_2659_, v_givenNameView_2670_, v___x_2673_);
if (lean_obj_tag(v___x_2674_) == 0)
{
if (lean_obj_tag(v_n_2660_) == 1)
{
lean_object* v_pre_2675_; lean_object* v_str_2676_; lean_object* v___f_2677_; 
v_pre_2675_ = lean_ctor_get(v_n_2660_, 0);
lean_inc(v_pre_2675_);
v_str_2676_ = lean_ctor_get(v_n_2660_, 1);
lean_inc_ref(v_str_2676_);
lean_dec_ref(v_n_2660_);
lean_inc(v_pre_2675_);
lean_inc_ref(v_findLocalDecl_x3f_2659_);
lean_inc_ref(v_view_2658_);
lean_inc(v_inst_2657_);
lean_inc_ref(v_inst_2656_);
lean_inc(v_inst_2655_);
lean_inc_ref(v_inst_2654_);
lean_inc_ref(v_inst_2653_);
lean_inc_ref(v_inst_2652_);
lean_inc(v_projs_2661_);
lean_inc_ref(v_str_2676_);
v___f_2677_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2677_, 0, v_str_2676_);
lean_closure_set(v___f_2677_, 1, v_projs_2661_);
lean_closure_set(v___f_2677_, 2, v_inst_2652_);
lean_closure_set(v___f_2677_, 3, v_inst_2653_);
lean_closure_set(v___f_2677_, 4, v_inst_2654_);
lean_closure_set(v___f_2677_, 5, v_inst_2655_);
lean_closure_set(v___f_2677_, 6, v_inst_2656_);
lean_closure_set(v___f_2677_, 7, v_inst_2657_);
lean_closure_set(v___f_2677_, 8, v_view_2658_);
lean_closure_set(v___f_2677_, 9, v_findLocalDecl_x3f_2659_);
lean_closure_set(v___f_2677_, 10, v_pre_2675_);
if (v_globalDeclFound_2662_ == 0)
{
uint8_t v_globalDeclFoundNext_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___f_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_inc(v_toBind_2667_);
lean_dec_ref(v_str_2676_);
lean_dec(v_pre_2675_);
lean_dec(v_projs_2661_);
lean_dec_ref(v_findLocalDecl_x3f_2659_);
lean_dec_ref(v_view_2658_);
v_globalDeclFoundNext_2678_ = 1;
v___x_2679_ = lean_box(v_globalDeclFoundNext_2678_);
v___x_2680_ = lean_box(v_globalDeclFound_2662_);
v___f_2681_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2681_, 0, v___f_2669_);
lean_closure_set(v___f_2681_, 1, v___f_2677_);
lean_closure_set(v___f_2681_, 2, v___x_2679_);
lean_closure_set(v___f_2681_, 3, v___x_2680_);
v___x_2682_ = l_Lean_MacroScopesView_review(v_givenNameView_2670_);
v___x_2683_ = l_Lean_resolveGlobalName___redArg(v_inst_2652_, v_inst_2653_, v_inst_2654_, v_inst_2655_, v_inst_2656_, v_inst_2657_, v___x_2682_, v_globalDeclFound_2662_);
v___x_2684_ = lean_apply_4(v_toBind_2667_, lean_box(0), lean_box(0), v___x_2683_, v___f_2681_);
return v___x_2684_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref(v___f_2677_);
lean_dec_ref(v_givenNameView_2670_);
v___x_2685_ = lean_box(0);
v___x_2686_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2676_, v_projs_2661_, v_inst_2652_, v_inst_2653_, v_inst_2654_, v_inst_2655_, v_inst_2656_, v_inst_2657_, v_view_2658_, v_findLocalDecl_x3f_2659_, v_pre_2675_, v___x_2685_, v_globalDeclFound_2662_);
return v___x_2686_;
}
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_inc(v_toPure_2668_);
lean_dec_ref(v_givenNameView_2670_);
lean_dec(v_projs_2661_);
lean_dec(v_n_2660_);
lean_dec_ref(v_findLocalDecl_x3f_2659_);
lean_dec_ref(v_view_2658_);
lean_dec(v_inst_2657_);
lean_dec_ref(v_inst_2656_);
lean_dec(v_inst_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_inst_2653_);
lean_dec_ref(v_inst_2652_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_apply_2(v_toPure_2668_, lean_box(0), v___x_2687_);
return v___x_2688_;
}
}
else
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2705_; 
lean_inc(v_toPure_2668_);
lean_dec_ref(v_givenNameView_2670_);
lean_dec(v_n_2660_);
lean_dec_ref(v_findLocalDecl_x3f_2659_);
lean_dec_ref(v_view_2658_);
lean_dec(v_inst_2657_);
lean_dec_ref(v_inst_2656_);
lean_dec(v_inst_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_inst_2653_);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_inst_2652_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2706_ = lean_ctor_get(v_inst_2652_, 1);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_inst_2652_, 0);
lean_dec(v_unused_2707_);
v___x_2690_ = v_inst_2652_;
v_isShared_2691_ = v_isSharedCheck_2705_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v_inst_2652_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2705_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_val_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2704_; 
v_val_2692_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2694_ = v___x_2674_;
v_isShared_2695_ = v_isSharedCheck_2704_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_val_2692_);
lean_dec(v___x_2674_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2704_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = l_Lean_LocalDecl_toExpr(v_val_2692_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 1, v_projs_2661_);
lean_ctor_set(v___x_2690_, 0, v___x_2696_);
v___x_2698_ = v___x_2690_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_projs_2661_);
v___x_2698_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2698_);
v___x_2700_ = v___x_2694_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_apply_2(v_toPure_2668_, lean_box(0), v___x_2700_);
return v___x_2701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2710_, lean_object* v_projs_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_view_2718_, lean_object* v_findLocalDecl_x3f_2719_, lean_object* v_pre_2720_, lean_object* v_____r_2721_, uint8_t v_globalDeclFoundNext_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_str_2710_);
lean_ctor_set(v___x_2723_, 1, v_projs_2711_);
v___x_2724_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_inst_2715_, v_inst_2716_, v_inst_2717_, v_view_2718_, v_findLocalDecl_x3f_2719_, v_pre_2720_, v___x_2723_, v_globalDeclFoundNext_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_view_2731_, lean_object* v_findLocalDecl_x3f_2732_, lean_object* v_n_2733_, lean_object* v_projs_2734_, lean_object* v_globalDeclFound_2735_){
_start:
{
uint8_t v_globalDeclFound_boxed_2736_; lean_object* v_res_2737_; 
v_globalDeclFound_boxed_2736_ = lean_unbox(v_globalDeclFound_2735_);
v_res_2737_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2725_, v_inst_2726_, v_inst_2727_, v_inst_2728_, v_inst_2729_, v_inst_2730_, v_view_2731_, v_findLocalDecl_x3f_2732_, v_n_2733_, v_projs_2734_, v_globalDeclFound_boxed_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_view_2745_, lean_object* v_findLocalDecl_x3f_2746_, lean_object* v_n_2747_, lean_object* v_projs_2748_, uint8_t v_globalDeclFound_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_inst_2744_, v_view_2745_, v_findLocalDecl_x3f_2746_, v_n_2747_, v_projs_2748_, v_globalDeclFound_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_view_2758_, lean_object* v_findLocalDecl_x3f_2759_, lean_object* v_n_2760_, lean_object* v_projs_2761_, lean_object* v_globalDeclFound_2762_){
_start:
{
uint8_t v_globalDeclFound_boxed_2763_; lean_object* v_res_2764_; 
v_globalDeclFound_boxed_2763_ = lean_unbox(v_globalDeclFound_2762_);
v_res_2764_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2751_, v_inst_2752_, v_inst_2753_, v_inst_2754_, v_inst_2755_, v_inst_2756_, v_inst_2757_, v_view_2758_, v_findLocalDecl_x3f_2759_, v_n_2760_, v_projs_2761_, v_globalDeclFound_boxed_2763_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2765_, lean_object* v_givenNameView_2766_, lean_object* v_fullDeclName_2767_, lean_object* v_ns_2768_){
_start:
{
lean_object* v_name_2769_; lean_object* v_imported_2770_; lean_object* v_ctx_2771_; lean_object* v_scopes_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_name_2769_ = lean_ctor_get(v_givenNameView_2766_, 0);
v_imported_2770_ = lean_ctor_get(v_givenNameView_2766_, 1);
v_ctx_2771_ = lean_ctor_get(v_givenNameView_2766_, 2);
v_scopes_2772_ = lean_ctor_get(v_givenNameView_2766_, 3);
lean_inc(v_name_2769_);
lean_inc(v_ns_2768_);
v___x_2773_ = l_Lean_Name_append(v_ns_2768_, v_name_2769_);
lean_inc(v_scopes_2772_);
lean_inc(v_ctx_2771_);
lean_inc(v_imported_2770_);
v___x_2774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_imported_2770_);
lean_ctor_set(v___x_2774_, 2, v_ctx_2771_);
lean_ctor_set(v___x_2774_, 3, v_scopes_2772_);
v___x_2775_ = l_Lean_MacroScopesView_review(v___x_2774_);
v___x_2776_ = lean_name_eq(v___x_2775_, v_fullDeclName_2767_);
lean_dec(v___x_2775_);
if (v___x_2776_ == 0)
{
if (lean_obj_tag(v_ns_2768_) == 1)
{
lean_object* v_pre_2777_; 
v_pre_2777_ = lean_ctor_get(v_ns_2768_, 0);
lean_inc(v_pre_2777_);
lean_dec_ref(v_ns_2768_);
v_ns_2768_ = v_pre_2777_;
goto _start;
}
else
{
lean_object* v___x_2779_; 
lean_dec(v_ns_2768_);
lean_dec_ref(v_givenNameView_2766_);
lean_dec_ref(v_localDecl_2765_);
v___x_2779_ = lean_box(0);
return v___x_2779_;
}
}
else
{
lean_object* v___x_2780_; 
lean_dec(v_ns_2768_);
lean_dec_ref(v_givenNameView_2766_);
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_localDecl_2765_);
return v___x_2780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2781_, lean_object* v_givenNameView_2782_, lean_object* v_fullDeclName_2783_, lean_object* v_ns_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2781_, v_givenNameView_2782_, v_fullDeclName_2783_, v_ns_2784_);
lean_dec(v_fullDeclName_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2786_, lean_object* v_givenName_2787_){
_start:
{
lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2788_ = l_Lean_LocalDecl_userName(v_localDecl_2786_);
v___x_2789_ = lean_name_eq(v___x_2788_, v_givenName_2787_);
lean_dec(v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_dec_ref(v_localDecl_2786_);
v___x_2790_ = lean_box(0);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_localDecl_2786_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2792_, lean_object* v_givenName_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2792_, v_givenName_2793_);
lean_dec(v_givenName_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2795_, lean_object* v_givenName_2796_, uint8_t v_skipAuxDecl_2797_, lean_object* v___f_2798_, lean_object* v_auxDeclToFullName_2799_, lean_object* v_currNamespace_2800_, lean_object* v_givenNameView_2801_, lean_object* v_x_2802_){
_start:
{
if (lean_obj_tag(v_x_2802_) == 0)
{
lean_dec_ref(v_givenNameView_2801_);
lean_dec(v_currNamespace_2800_);
lean_dec(v_auxDeclToFullName_2799_);
lean_dec_ref(v___f_2798_);
lean_dec(v_givenName_2796_);
lean_dec_ref(v_matchLocalDecl_x3f_2795_);
return v_x_2802_;
}
else
{
lean_object* v_val_2803_; uint8_t v___x_2804_; 
v_val_2803_ = lean_ctor_get(v_x_2802_, 0);
v___x_2804_ = l_Lean_LocalDecl_isAuxDecl(v_val_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_inc(v_val_2803_);
lean_dec_ref(v_x_2802_);
lean_dec_ref(v_givenNameView_2801_);
lean_dec(v_currNamespace_2800_);
lean_dec(v_auxDeclToFullName_2799_);
lean_dec_ref(v___f_2798_);
v___x_2805_ = lean_apply_2(v_matchLocalDecl_x3f_2795_, v_val_2803_, v_givenName_2796_);
return v___x_2805_;
}
else
{
if (v_skipAuxDecl_2797_ == 0)
{
if (v___x_2804_ == 0)
{
lean_object* v___x_2806_; 
lean_dec_ref(v_x_2802_);
lean_dec_ref(v_givenNameView_2801_);
lean_dec(v_currNamespace_2800_);
lean_dec(v_auxDeclToFullName_2799_);
lean_dec_ref(v___f_2798_);
lean_dec(v_givenName_2796_);
lean_dec_ref(v_matchLocalDecl_x3f_2795_);
v___x_2806_ = lean_box(0);
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = l_Lean_LocalDecl_fvarId(v_val_2803_);
v___x_2808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2798_, v_auxDeclToFullName_2799_, v___x_2807_);
if (lean_obj_tag(v___x_2808_) == 1)
{
lean_object* v_val_2809_; lean_object* v_fullDeclView_2810_; lean_object* v___y_2812_; lean_object* v_name_2833_; lean_object* v___x_2834_; 
lean_dec(v_givenName_2796_);
lean_dec_ref(v_matchLocalDecl_x3f_2795_);
v_val_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_val_2809_);
lean_dec_ref(v___x_2808_);
v_fullDeclView_2810_ = l_Lean_extractMacroScopes(v_val_2809_);
v_name_2833_ = lean_ctor_get(v_fullDeclView_2810_, 0);
lean_inc(v_name_2833_);
lean_inc(v_name_2833_);
v___x_2834_ = lean_private_to_user_name(v_name_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
v___y_2812_ = v_name_2833_;
goto v___jp_2811_;
}
else
{
lean_object* v_val_2835_; 
lean_dec(v_name_2833_);
v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2835_);
lean_dec_ref(v___x_2834_);
v___y_2812_ = v_val_2835_;
goto v___jp_2811_;
}
v___jp_2811_:
{
lean_object* v_imported_2813_; lean_object* v_ctx_2814_; lean_object* v_scopes_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2831_; 
v_imported_2813_ = lean_ctor_get(v_fullDeclView_2810_, 1);
v_ctx_2814_ = lean_ctor_get(v_fullDeclView_2810_, 2);
v_scopes_2815_ = lean_ctor_get(v_fullDeclView_2810_, 3);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_fullDeclView_2810_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v_fullDeclView_2810_, 0);
lean_dec(v_unused_2832_);
v___x_2817_ = v_fullDeclView_2810_;
v_isShared_2818_ = v_isSharedCheck_2831_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_scopes_2815_);
lean_inc(v_ctx_2814_);
lean_inc(v_imported_2813_);
lean_dec(v_fullDeclView_2810_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2831_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_fullDeclView_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___y_2812_);
v_fullDeclView_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___y_2812_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_imported_2813_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_ctx_2814_);
lean_ctor_set(v_reuseFailAlloc_2830_, 3, v_scopes_2815_);
v_fullDeclView_2820_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v_fullDeclName_2821_; uint8_t v___x_2822_; 
lean_inc_ref(v_fullDeclView_2820_);
v_fullDeclName_2821_ = l_Lean_MacroScopesView_review(v_fullDeclView_2820_);
v___x_2822_ = l_Lean_Name_isPrefixOf(v_currNamespace_2800_, v_fullDeclName_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
lean_inc(v_val_2803_);
lean_dec_ref(v_fullDeclView_2820_);
lean_dec_ref(v_x_2802_);
v___x_2823_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2803_, v_givenNameView_2801_, v_fullDeclName_2821_, v_currNamespace_2800_);
lean_dec(v_fullDeclName_2821_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; lean_object* v_localDeclNameView_2825_; uint8_t v___x_2826_; 
lean_dec(v_fullDeclName_2821_);
lean_dec(v_currNamespace_2800_);
v___x_2824_ = l_Lean_LocalDecl_userName(v_val_2803_);
v_localDeclNameView_2825_ = l_Lean_extractMacroScopes(v___x_2824_);
v___x_2826_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2825_, v_givenNameView_2801_);
lean_dec_ref(v_localDeclNameView_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
lean_dec_ref(v_fullDeclView_2820_);
lean_dec_ref(v_x_2802_);
lean_dec_ref(v_givenNameView_2801_);
v___x_2827_ = lean_box(0);
return v___x_2827_;
}
else
{
uint8_t v___x_2828_; 
v___x_2828_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2801_, v_fullDeclView_2820_);
lean_dec_ref(v_fullDeclView_2820_);
lean_dec_ref(v_givenNameView_2801_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
lean_dec_ref(v_x_2802_);
v___x_2829_ = lean_box(0);
return v___x_2829_;
}
else
{
return v_x_2802_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2836_; 
lean_inc(v_val_2803_);
lean_dec(v___x_2808_);
lean_dec_ref(v_x_2802_);
lean_dec_ref(v_givenNameView_2801_);
lean_dec(v_currNamespace_2800_);
v___x_2836_ = lean_apply_2(v_matchLocalDecl_x3f_2795_, v_val_2803_, v_givenName_2796_);
return v___x_2836_;
}
}
}
else
{
lean_object* v___x_2837_; 
lean_dec_ref(v_x_2802_);
lean_dec_ref(v_givenNameView_2801_);
lean_dec(v_currNamespace_2800_);
lean_dec(v_auxDeclToFullName_2799_);
lean_dec_ref(v___f_2798_);
lean_dec(v_givenName_2796_);
lean_dec_ref(v_matchLocalDecl_x3f_2795_);
v___x_2837_ = lean_box(0);
return v___x_2837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2838_, lean_object* v_givenName_2839_, lean_object* v_skipAuxDecl_2840_, lean_object* v___f_2841_, lean_object* v_auxDeclToFullName_2842_, lean_object* v_currNamespace_2843_, lean_object* v_givenNameView_2844_, lean_object* v_x_2845_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2846_; lean_object* v_res_2847_; 
v_skipAuxDecl_boxed_2846_ = lean_unbox(v_skipAuxDecl_2840_);
v_res_2847_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2838_, v_givenName_2839_, v_skipAuxDecl_boxed_2846_, v___f_2841_, v_auxDeclToFullName_2842_, v_currNamespace_2843_, v_givenNameView_2844_, v_x_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2848_, lean_object* v_matchLocalDecl_x3f_2849_, lean_object* v_givenName_2850_, lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2851_) == 0)
{
lean_dec(v_givenName_2850_);
lean_dec_ref(v_matchLocalDecl_x3f_2849_);
return v_x_2851_;
}
else
{
lean_object* v_val_2852_; uint8_t v___x_2853_; 
v_val_2852_ = lean_ctor_get(v_x_2851_, 0);
lean_inc(v_val_2852_);
lean_dec_ref(v_x_2851_);
v___x_2853_ = l_Lean_LocalDecl_isAuxDecl(v_val_2852_);
if (v___x_2853_ == 0)
{
lean_dec(v_val_2852_);
lean_dec(v_givenName_2850_);
lean_dec_ref(v_matchLocalDecl_x3f_2849_);
lean_inc(v_localDecl_x3f_2848_);
return v_localDecl_x3f_2848_;
}
else
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_apply_2(v_matchLocalDecl_x3f_2849_, v_val_2852_, v_givenName_2850_);
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2855_, lean_object* v_matchLocalDecl_x3f_2856_, lean_object* v_givenName_2857_, lean_object* v_x_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2855_, v_matchLocalDecl_x3f_2856_, v_givenName_2857_, v_x_2858_);
lean_dec(v_localDecl_x3f_2855_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2879_, lean_object* v_matchLocalDecl_x3f_2880_, lean_object* v___f_2881_, lean_object* v_auxDeclToFullName_2882_, lean_object* v_currNamespace_2883_, lean_object* v_givenNameView_2884_, uint8_t v_skipAuxDecl_2885_){
_start:
{
lean_object* v_decls_2886_; lean_object* v_givenName_2887_; lean_object* v___x_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; lean_object* v_localDecl_x3f_2891_; 
v_decls_2886_ = lean_ctor_get(v_lctx_2879_, 1);
lean_inc_ref(v_decls_2886_);
lean_dec_ref(v_lctx_2879_);
lean_inc_ref(v_givenNameView_2884_);
v_givenName_2887_ = l_Lean_MacroScopesView_review(v_givenNameView_2884_);
v___x_2888_ = lean_box(v_skipAuxDecl_2885_);
lean_inc(v_givenName_2887_);
lean_inc_ref(v_matchLocalDecl_x3f_2880_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2889_, 0, v_matchLocalDecl_x3f_2880_);
lean_closure_set(v___f_2889_, 1, v_givenName_2887_);
lean_closure_set(v___f_2889_, 2, v___x_2888_);
lean_closure_set(v___f_2889_, 3, v___f_2881_);
lean_closure_set(v___f_2889_, 4, v_auxDeclToFullName_2882_);
lean_closure_set(v___f_2889_, 5, v_currNamespace_2883_);
lean_closure_set(v___f_2889_, 6, v_givenNameView_2884_);
v___x_2890_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
lean_inc_ref(v_decls_2886_);
v_localDecl_x3f_2891_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2890_, v_decls_2886_, v___f_2889_);
if (lean_obj_tag(v_localDecl_x3f_2891_) == 0)
{
if (v_skipAuxDecl_2885_ == 0)
{
lean_object* v___f_2892_; lean_object* v___x_2893_; 
v___f_2892_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2892_, 0, v_localDecl_x3f_2891_);
lean_closure_set(v___f_2892_, 1, v_matchLocalDecl_x3f_2880_);
lean_closure_set(v___f_2892_, 2, v_givenName_2887_);
v___x_2893_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2890_, v_decls_2886_, v___f_2892_);
return v___x_2893_;
}
else
{
lean_dec(v_givenName_2887_);
lean_dec_ref(v_decls_2886_);
lean_dec_ref(v_matchLocalDecl_x3f_2880_);
return v_localDecl_x3f_2891_;
}
}
else
{
lean_dec(v_givenName_2887_);
lean_dec_ref(v_decls_2886_);
lean_dec_ref(v_matchLocalDecl_x3f_2880_);
return v_localDecl_x3f_2891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2894_, lean_object* v_matchLocalDecl_x3f_2895_, lean_object* v___f_2896_, lean_object* v_auxDeclToFullName_2897_, lean_object* v_currNamespace_2898_, lean_object* v_givenNameView_2899_, lean_object* v_skipAuxDecl_2900_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2901_; lean_object* v_res_2902_; 
v_skipAuxDecl_boxed_2901_ = lean_unbox(v_skipAuxDecl_2900_);
v_res_2902_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2894_, v_matchLocalDecl_x3f_2895_, v___f_2896_, v_auxDeclToFullName_2897_, v_currNamespace_2898_, v_givenNameView_2899_, v_skipAuxDecl_boxed_2901_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2903_, lean_object* v_lctx_2904_, lean_object* v_matchLocalDecl_x3f_2905_, lean_object* v___f_2906_, lean_object* v_auxDeclToFullName_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_currNamespace_2914_){
_start:
{
lean_object* v_view_2915_; lean_object* v_name_2916_; lean_object* v_findLocalDecl_x3f_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
v_view_2915_ = l_Lean_extractMacroScopes(v_n_2903_);
v_name_2916_ = lean_ctor_get(v_view_2915_, 0);
lean_inc(v_name_2916_);
v_findLocalDecl_x3f_2917_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2917_, 0, v_lctx_2904_);
lean_closure_set(v_findLocalDecl_x3f_2917_, 1, v_matchLocalDecl_x3f_2905_);
lean_closure_set(v_findLocalDecl_x3f_2917_, 2, v___f_2906_);
lean_closure_set(v_findLocalDecl_x3f_2917_, 3, v_auxDeclToFullName_2907_);
lean_closure_set(v_findLocalDecl_x3f_2917_, 4, v_currNamespace_2914_);
v___x_2918_ = lean_box(0);
v___x_2919_ = 0;
v___x_2920_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2908_, v_inst_2909_, v_inst_2910_, v_inst_2911_, v_inst_2912_, v_inst_2913_, v_view_2915_, v_findLocalDecl_x3f_2917_, v_name_2916_, v___x_2918_, v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2921_, lean_object* v_n_2922_, lean_object* v_lctx_2923_, lean_object* v_matchLocalDecl_x3f_2924_, lean_object* v___f_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_toBind_2931_, lean_object* v_____do__lift_2932_){
_start:
{
lean_object* v_auxDeclToFullName_2933_; lean_object* v_getCurrNamespace_2934_; lean_object* v___f_2935_; lean_object* v___x_2936_; 
v_auxDeclToFullName_2933_ = lean_ctor_get(v_____do__lift_2932_, 2);
lean_inc(v_auxDeclToFullName_2933_);
lean_dec_ref(v_____do__lift_2932_);
v_getCurrNamespace_2934_ = lean_ctor_get(v_inst_2921_, 0);
lean_inc(v_getCurrNamespace_2934_);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2935_, 0, v_n_2922_);
lean_closure_set(v___f_2935_, 1, v_lctx_2923_);
lean_closure_set(v___f_2935_, 2, v_matchLocalDecl_x3f_2924_);
lean_closure_set(v___f_2935_, 3, v___f_2925_);
lean_closure_set(v___f_2935_, 4, v_auxDeclToFullName_2933_);
lean_closure_set(v___f_2935_, 5, v_inst_2926_);
lean_closure_set(v___f_2935_, 6, v_inst_2921_);
lean_closure_set(v___f_2935_, 7, v_inst_2927_);
lean_closure_set(v___f_2935_, 8, v_inst_2928_);
lean_closure_set(v___f_2935_, 9, v_inst_2929_);
lean_closure_set(v___f_2935_, 10, v_inst_2930_);
v___x_2936_ = lean_apply_4(v_toBind_2931_, lean_box(0), lean_box(0), v_getCurrNamespace_2934_, v___f_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2937_, lean_object* v_n_2938_, lean_object* v_matchLocalDecl_x3f_2939_, lean_object* v___f_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_toBind_2946_, lean_object* v_inst_2947_, lean_object* v_lctx_2948_){
_start:
{
lean_object* v___f_2949_; lean_object* v___x_2950_; 
lean_inc(v_toBind_2946_);
v___f_2949_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2949_, 0, v_inst_2937_);
lean_closure_set(v___f_2949_, 1, v_n_2938_);
lean_closure_set(v___f_2949_, 2, v_lctx_2948_);
lean_closure_set(v___f_2949_, 3, v_matchLocalDecl_x3f_2939_);
lean_closure_set(v___f_2949_, 4, v___f_2940_);
lean_closure_set(v___f_2949_, 5, v_inst_2941_);
lean_closure_set(v___f_2949_, 6, v_inst_2942_);
lean_closure_set(v___f_2949_, 7, v_inst_2943_);
lean_closure_set(v___f_2949_, 8, v_inst_2944_);
lean_closure_set(v___f_2949_, 9, v_inst_2945_);
lean_closure_set(v___f_2949_, 10, v_toBind_2946_);
v___x_2950_ = lean_apply_4(v_toBind_2946_, lean_box(0), lean_box(0), v_inst_2947_, v___f_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_n_2960_){
_start:
{
lean_object* v_toBind_2961_; lean_object* v___f_2962_; lean_object* v_matchLocalDecl_x3f_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; 
v_toBind_2961_ = lean_ctor_get(v_inst_2953_, 1);
lean_inc(v_toBind_2961_);
v___f_2962_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2963_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2959_);
lean_inc(v_toBind_2961_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2964_, 0, v_inst_2954_);
lean_closure_set(v___f_2964_, 1, v_n_2960_);
lean_closure_set(v___f_2964_, 2, v_matchLocalDecl_x3f_2963_);
lean_closure_set(v___f_2964_, 3, v___f_2962_);
lean_closure_set(v___f_2964_, 4, v_inst_2953_);
lean_closure_set(v___f_2964_, 5, v_inst_2955_);
lean_closure_set(v___f_2964_, 6, v_inst_2956_);
lean_closure_set(v___f_2964_, 7, v_inst_2957_);
lean_closure_set(v___f_2964_, 8, v_inst_2958_);
lean_closure_set(v___f_2964_, 9, v_toBind_2961_);
lean_closure_set(v___f_2964_, 10, v_inst_2959_);
v___x_2965_ = lean_apply_4(v_toBind_2961_, lean_box(0), lean_box(0), v_inst_2959_, v___f_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_n_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_resolveLocalName___redArg(v_inst_2967_, v_inst_2968_, v_inst_2969_, v_inst_2970_, v_inst_2971_, v_inst_2972_, v_inst_2973_, v_n_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2976_, uint8_t v_____do__lift_2977_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = lean_box(v_____do__lift_2977_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
v___x_2980_ = lean_apply_2(v_toPure_2976_, lean_box(0), v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2981_, lean_object* v_____do__lift_2982_){
_start:
{
uint8_t v_____do__lift_1160__boxed_2983_; lean_object* v_res_2984_; 
v_____do__lift_1160__boxed_2983_ = lean_unbox(v_____do__lift_2982_);
v_res_2984_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2981_, v_____do__lift_1160__boxed_2983_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2985_, lean_object* v___y_2986_, lean_object* v_____do__lift_2987_){
_start:
{
if (lean_obj_tag(v_____do__lift_2987_) == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec(v___y_2986_);
v___x_2988_ = lean_box(0);
v___x_2989_ = lean_apply_2(v_toPure_2985_, lean_box(0), v___x_2988_);
return v___x_2989_;
}
else
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2997_; 
v_isSharedCheck_2997_ = !lean_is_exclusive(v_____do__lift_2987_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v_____do__lift_2987_, 0);
lean_dec(v_unused_2998_);
v___x_2991_ = v_____do__lift_2987_;
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v_____do__lift_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___y_2986_);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___y_2986_);
v___x_2994_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_apply_2(v_toPure_2985_, lean_box(0), v___x_2994_);
return v___x_2995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_3001_, lean_object* v_toBind_3002_, lean_object* v___f_3003_, lean_object* v_____do__lift_3004_){
_start:
{
if (lean_obj_tag(v_____do__lift_3004_) == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec(v___f_3003_);
lean_dec(v_toBind_3002_);
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_apply_2(v_toPure_3001_, lean_box(0), v___x_3005_);
return v___x_3006_;
}
else
{
lean_object* v_val_3007_; uint8_t v___x_3008_; 
v_val_3007_ = lean_ctor_get(v_____do__lift_3004_, 0);
v___x_3008_ = lean_unbox(v_val_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_apply_2(v_toPure_3001_, lean_box(0), v___x_3009_);
v___x_3011_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v___x_3010_, v___f_3003_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3013_ = lean_apply_2(v_toPure_3001_, lean_box(0), v___x_3012_);
v___x_3014_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v___x_3013_, v___f_3003_);
return v___x_3014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_3015_, lean_object* v_toBind_3016_, lean_object* v___f_3017_, lean_object* v_____do__lift_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_3015_, v_toBind_3016_, v___f_3017_, v_____do__lift_3018_);
lean_dec(v_____do__lift_3018_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_3020_, lean_object* v_filter_3021_, lean_object* v___y_3022_, lean_object* v_toBind_3023_, lean_object* v___f_3024_, lean_object* v___f_3025_, lean_object* v_____do__lift_3026_){
_start:
{
if (lean_obj_tag(v_____do__lift_3026_) == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec(v___f_3025_);
lean_dec(v___f_3024_);
lean_dec(v_toBind_3023_);
lean_dec(v___y_3022_);
lean_dec(v_filter_3021_);
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_apply_2(v_toPure_3020_, lean_box(0), v___x_3027_);
return v___x_3028_;
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v_toPure_3020_);
v___x_3029_ = lean_apply_1(v_filter_3021_, v___y_3022_);
lean_inc(v_toBind_3023_);
v___x_3030_ = lean_apply_4(v_toBind_3023_, lean_box(0), lean_box(0), v___x_3029_, v___f_3024_);
v___x_3031_ = lean_apply_4(v_toBind_3023_, lean_box(0), lean_box(0), v___x_3030_, v___f_3025_);
return v___x_3031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3032_, lean_object* v_filter_3033_, lean_object* v___y_3034_, lean_object* v_toBind_3035_, lean_object* v___f_3036_, lean_object* v___f_3037_, lean_object* v_____do__lift_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3032_, v_filter_3033_, v___y_3034_, v_toBind_3035_, v___f_3036_, v___f_3037_, v_____do__lift_3038_);
lean_dec(v_____do__lift_3038_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3040_, lean_object* v_n_u2080_3041_, lean_object* v_toBind_3042_, lean_object* v___f_3043_, lean_object* v_____do__lift_3044_){
_start:
{
if (lean_obj_tag(v_____do__lift_3044_) == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec(v___f_3043_);
lean_dec(v_toBind_3042_);
v___x_3048_ = lean_box(0);
v___x_3049_ = lean_apply_2(v_toPure_3040_, lean_box(0), v___x_3048_);
return v___x_3049_;
}
else
{
lean_object* v_val_3050_; 
v_val_3050_ = lean_ctor_get(v_____do__lift_3044_, 0);
if (lean_obj_tag(v_val_3050_) == 1)
{
lean_object* v_tail_3051_; 
v_tail_3051_ = lean_ctor_get(v_val_3050_, 1);
if (lean_obj_tag(v_tail_3051_) == 0)
{
lean_object* v_head_3052_; lean_object* v_fst_3053_; uint8_t v___x_3054_; 
v_head_3052_ = lean_ctor_get(v_val_3050_, 0);
v_fst_3053_ = lean_ctor_get(v_head_3052_, 0);
v___x_3054_ = lean_name_eq(v_fst_3053_, v_n_u2080_3041_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_apply_2(v_toPure_3040_, lean_box(0), v___x_3055_);
v___x_3057_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v___x_3056_, v___f_3043_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3059_ = lean_apply_2(v_toPure_3040_, lean_box(0), v___x_3058_);
v___x_3060_ = lean_apply_4(v_toBind_3042_, lean_box(0), lean_box(0), v___x_3059_, v___f_3043_);
return v___x_3060_;
}
}
else
{
lean_dec(v___f_3043_);
lean_dec(v_toBind_3042_);
goto v___jp_3045_;
}
}
else
{
lean_dec(v___f_3043_);
lean_dec(v_toBind_3042_);
goto v___jp_3045_;
}
}
v___jp_3045_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_apply_2(v_toPure_3040_, lean_box(0), v___x_3046_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3061_, lean_object* v_n_u2080_3062_, lean_object* v_toBind_3063_, lean_object* v___f_3064_, lean_object* v_____do__lift_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3061_, v_n_u2080_3062_, v_toBind_3063_, v___f_3064_, v_____do__lift_3065_);
lean_dec(v_____do__lift_3065_);
lean_dec(v_n_u2080_3062_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v_n_u2080_3073_, lean_object* v_filter_3074_, lean_object* v_view_x3f_3075_, lean_object* v_n_3076_){
_start:
{
lean_object* v___f_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_toApplicative_3089_; lean_object* v_getEnv_3090_; lean_object* v_modifyEnv_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3129_; 
lean_inc_ref(v_inst_3067_);
v___f_3077_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3077_, 0, v_inst_3067_);
lean_inc_ref(v_inst_3067_);
v___f_3078_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3078_, 0, v_inst_3067_);
lean_inc_ref(v_inst_3067_);
v___f_3079_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3079_, 0, v_inst_3067_);
lean_inc_ref(v_inst_3067_);
v___f_3080_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3080_, 0, v_inst_3067_);
lean_inc_ref(v_inst_3067_);
v___f_3081_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3081_, 0, v_inst_3067_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___f_3077_);
lean_ctor_set(v___x_3082_, 1, v___f_3078_);
lean_inc_ref(v_inst_3067_);
v___x_3083_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3083_, 0, lean_box(0));
lean_closure_set(v___x_3083_, 1, v_inst_3067_);
v___x_3084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
lean_ctor_set(v___x_3084_, 2, v___f_3079_);
lean_ctor_set(v___x_3084_, 3, v___f_3080_);
lean_ctor_set(v___x_3084_, 4, v___f_3081_);
lean_inc_ref(v_inst_3067_);
v___x_3085_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3085_, 0, lean_box(0));
lean_closure_set(v___x_3085_, 1, v_inst_3067_);
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3084_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
lean_inc_ref(v_inst_3067_);
v___x_3087_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3087_, 0, lean_box(0));
lean_closure_set(v___x_3087_, 1, v_inst_3067_);
lean_inc_ref(v___x_3087_);
v___x_3088_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3087_, v_inst_3068_);
v_toApplicative_3089_ = lean_ctor_get(v_inst_3067_, 0);
lean_inc_ref(v_toApplicative_3089_);
v_getEnv_3090_ = lean_ctor_get(v_inst_3069_, 0);
v_modifyEnv_3091_ = lean_ctor_get(v_inst_3069_, 1);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_inst_3069_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3093_ = v_inst_3069_;
v_isShared_3094_ = v_isSharedCheck_3129_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_modifyEnv_3091_);
lean_inc(v_getEnv_3090_);
lean_dec(v_inst_3069_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3129_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_toBind_3095_; lean_object* v_toPure_3096_; lean_object* v___f_3097_; lean_object* v___f_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v_toBind_3095_ = lean_ctor_get(v_inst_3067_, 1);
lean_inc(v_toBind_3095_);
lean_dec_ref(v_inst_3067_);
v_toPure_3096_ = lean_ctor_get(v_toApplicative_3089_, 1);
lean_inc(v_toPure_3096_);
lean_dec_ref(v_toApplicative_3089_);
lean_inc_ref(v___x_3087_);
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3097_, 0, v_modifyEnv_3091_);
lean_closure_set(v___f_3097_, 1, v___x_3087_);
lean_inc(v_toPure_3096_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3098_, 0, v_toPure_3096_);
lean_inc(v_toPure_3096_);
v___f_3099_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3099_, 0, v_toPure_3096_);
lean_inc(v_toBind_3095_);
lean_inc_ref(v___f_3099_);
v___x_3100_ = lean_apply_4(v_toBind_3095_, lean_box(0), lean_box(0), v_getEnv_3090_, v___f_3099_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 1, v___f_3097_);
lean_ctor_set(v___x_3093_, 0, v___x_3100_);
v___x_3102_ = v___x_3093_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___f_3097_);
v___x_3102_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; lean_object* v___y_3107_; 
lean_inc(v_toBind_3095_);
v___x_3103_ = lean_apply_4(v_toBind_3095_, lean_box(0), lean_box(0), v_inst_3070_, v___f_3099_);
lean_inc_ref(v___x_3087_);
v___x_3104_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3087_, v_inst_3071_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3105_, 0, v_inst_3072_);
lean_closure_set(v___f_3105_, 1, v___x_3087_);
if (lean_obj_tag(v_view_x3f_3075_) == 1)
{
lean_object* v_val_3115_; lean_object* v_imported_3116_; lean_object* v_ctx_3117_; lean_object* v_scopes_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3126_; 
v_val_3115_ = lean_ctor_get(v_view_x3f_3075_, 0);
lean_inc(v_val_3115_);
lean_dec_ref(v_view_x3f_3075_);
v_imported_3116_ = lean_ctor_get(v_val_3115_, 1);
v_ctx_3117_ = lean_ctor_get(v_val_3115_, 2);
v_scopes_3118_ = lean_ctor_get(v_val_3115_, 3);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_val_3115_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v_val_3115_, 0);
lean_dec(v_unused_3127_);
v___x_3120_ = v_val_3115_;
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_scopes_3118_);
lean_inc(v_ctx_3117_);
lean_inc(v_imported_3116_);
lean_dec(v_val_3115_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v_n_3076_);
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_n_3076_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_imported_3116_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_ctx_3117_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_scopes_3118_);
v___x_3123_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_MacroScopesView_review(v___x_3123_);
v___y_3107_ = v___x_3124_;
goto v___jp_3106_;
}
}
}
else
{
lean_dec(v_view_x3f_3075_);
v___y_3107_ = v_n_3076_;
goto v___jp_3106_;
}
v___jp_3106_:
{
lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___f_3110_; lean_object* v___f_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_inc(v___y_3107_);
lean_inc(v_toPure_3096_);
v___f_3108_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3108_, 0, v_toPure_3096_);
lean_closure_set(v___f_3108_, 1, v___y_3107_);
lean_inc(v_toBind_3095_);
lean_inc(v_toPure_3096_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3109_, 0, v_toPure_3096_);
lean_closure_set(v___f_3109_, 1, v_toBind_3095_);
lean_closure_set(v___f_3109_, 2, v___f_3108_);
lean_inc(v_toBind_3095_);
lean_inc(v___y_3107_);
lean_inc(v_toPure_3096_);
v___f_3110_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3110_, 0, v_toPure_3096_);
lean_closure_set(v___f_3110_, 1, v_filter_3074_);
lean_closure_set(v___f_3110_, 2, v___y_3107_);
lean_closure_set(v___f_3110_, 3, v_toBind_3095_);
lean_closure_set(v___f_3110_, 4, v___f_3098_);
lean_closure_set(v___f_3110_, 5, v___f_3109_);
lean_inc(v_toBind_3095_);
v___f_3111_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3111_, 0, v_toPure_3096_);
lean_closure_set(v___f_3111_, 1, v_n_u2080_3073_);
lean_closure_set(v___f_3111_, 2, v_toBind_3095_);
lean_closure_set(v___f_3111_, 3, v___f_3110_);
v___x_3112_ = 0;
v___x_3113_ = l_Lean_resolveGlobalName___redArg(v___x_3086_, v___x_3088_, v___x_3102_, v___x_3103_, v___x_3104_, v___f_3105_, v___y_3107_, v___x_3112_);
v___x_3114_ = lean_apply_4(v_toBind_3095_, lean_box(0), lean_box(0), v___x_3113_, v___f_3111_);
return v___x_3114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3130_, lean_object* v_inst_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_n_u2080_3137_, lean_object* v_filter_3138_, lean_object* v_view_x3f_3139_, lean_object* v_n_3140_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3131_, v_inst_3132_, v_inst_3133_, v_inst_3134_, v_inst_3135_, v_inst_3136_, v_n_u2080_3137_, v_filter_3138_, v_view_x3f_3139_, v_n_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3146_, lean_object* v_____x_3147_){
_start:
{
if (lean_obj_tag(v_____x_3147_) == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3149_ = lean_apply_2(v_toPure_3146_, lean_box(0), v___x_3148_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_apply_2(v_toPure_3146_, lean_box(0), v_____x_3147_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3151_, lean_object* v_____do__lift_3152_){
_start:
{
if (lean_obj_tag(v_____do__lift_3152_) == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3153_);
return v___x_3154_;
}
else
{
lean_object* v_val_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3164_; 
v_val_3155_ = lean_ctor_get(v_____do__lift_3152_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_____do__lift_3152_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3157_ = v_____do__lift_3152_;
v_isShared_3158_ = v_isSharedCheck_3164_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_val_3155_);
lean_dec(v_____do__lift_3152_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3164_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_val_3155_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3161_);
return v___x_3162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3165_, lean_object* v___x_3166_, lean_object* v_____do__lift_3167_){
_start:
{
if (lean_obj_tag(v_____do__lift_3167_) == 0)
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_apply_2(v_toPure_3165_, lean_box(0), v___x_3166_);
return v___x_3168_;
}
else
{
lean_object* v_val_3169_; lean_object* v_fst_3170_; lean_object* v___x_3171_; 
lean_dec(v___x_3166_);
v_val_3169_ = lean_ctor_get(v_____do__lift_3167_, 0);
lean_inc(v_val_3169_);
lean_dec_ref(v_____do__lift_3167_);
v_fst_3170_ = lean_ctor_get(v_val_3169_, 0);
lean_inc(v_fst_3170_);
lean_dec(v_val_3169_);
v___x_3171_ = lean_apply_2(v_toPure_3165_, lean_box(0), v_fst_3170_);
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3172_, lean_object* v___x_3173_, lean_object* v___x_3174_, lean_object* v_____do__lift_3175_){
_start:
{
if (lean_obj_tag(v_____do__lift_3175_) == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec(v___x_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v___x_3177_ = lean_apply_2(v_toPure_3172_, lean_box(0), v___x_3176_);
return v___x_3177_;
}
else
{
lean_object* v_val_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3209_; 
v_val_3178_ = lean_ctor_get(v_____do__lift_3175_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_____do__lift_3175_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3180_ = v_____do__lift_3175_;
v_isShared_3181_ = v_isSharedCheck_3209_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_val_3178_);
lean_dec(v_____do__lift_3175_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3209_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
if (lean_obj_tag(v_val_3178_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v___x_3174_);
v_a_3182_ = lean_ctor_get(v_val_3178_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_val_3178_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3184_ = v_val_3178_;
v_isShared_3185_ = v_isSharedCheck_3195_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v_val_3178_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3195_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v_a_3182_);
v___x_3187_ = v___x_3180_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set(v___x_3188_, 1, v___x_3173_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3188_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
v___x_3192_ = lean_apply_2(v_toPure_3172_, lean_box(0), v___x_3191_);
return v___x_3192_;
}
}
}
}
else
{
lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3207_; 
v_isSharedCheck_3207_ = !lean_is_exclusive(v_val_3178_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v_val_3178_, 0);
lean_dec(v_unused_3208_);
v___x_3197_ = v_val_3178_;
v_isShared_3198_ = v_isSharedCheck_3207_;
goto v_resetjp_3196_;
}
else
{
lean_dec(v_val_3178_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3207_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3174_);
lean_ctor_set(v___x_3199_, 1, v___x_3173_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3201_);
v___x_3203_ = v___x_3180_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_apply_2(v_toPure_3172_, lean_box(0), v___x_3203_);
return v___x_3204_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3210_, lean_object* v___x_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_inst_3217_, lean_object* v_n_u2080_3218_, lean_object* v_filter_3219_, lean_object* v_view_x3f_3220_, lean_object* v_toBind_3221_, lean_object* v___f_3222_, lean_object* v___f_3223_, lean_object* v_a_3224_, lean_object* v_x_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_snd_3227_; lean_object* v___x_3228_; lean_object* v___f_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_snd_3227_ = lean_ctor_get(v___y_3226_, 1);
lean_inc(v_snd_3227_);
lean_dec_ref(v___y_3226_);
v___x_3228_ = l_Lean_Name_appendCore(v_a_3224_, v_snd_3227_);
lean_inc(v___x_3228_);
v___f_3229_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3229_, 0, v_toPure_3210_);
lean_closure_set(v___f_3229_, 1, v___x_3228_);
lean_closure_set(v___f_3229_, 2, v___x_3211_);
v___x_3230_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3212_, v_inst_3213_, v_inst_3214_, v_inst_3215_, v_inst_3216_, v_inst_3217_, v_n_u2080_3218_, v_filter_3219_, v_view_x3f_3220_, v___x_3228_);
lean_inc(v_toBind_3221_);
v___x_3231_ = lean_apply_4(v_toBind_3221_, lean_box(0), lean_box(0), v___x_3230_, v___f_3222_);
lean_inc(v_toBind_3221_);
v___x_3232_ = lean_apply_4(v_toBind_3221_, lean_box(0), lean_box(0), v___x_3231_, v___f_3223_);
v___x_3233_ = lean_apply_4(v_toBind_3221_, lean_box(0), lean_box(0), v___x_3232_, v___f_3229_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3234_ = _args[0];
lean_object* v___x_3235_ = _args[1];
lean_object* v_inst_3236_ = _args[2];
lean_object* v_inst_3237_ = _args[3];
lean_object* v_inst_3238_ = _args[4];
lean_object* v_inst_3239_ = _args[5];
lean_object* v_inst_3240_ = _args[6];
lean_object* v_inst_3241_ = _args[7];
lean_object* v_n_u2080_3242_ = _args[8];
lean_object* v_filter_3243_ = _args[9];
lean_object* v_view_x3f_3244_ = _args[10];
lean_object* v_toBind_3245_ = _args[11];
lean_object* v___f_3246_ = _args[12];
lean_object* v___f_3247_ = _args[13];
lean_object* v_a_3248_ = _args[14];
lean_object* v_x_3249_ = _args[15];
lean_object* v___y_3250_ = _args[16];
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3234_, v___x_3235_, v_inst_3236_, v_inst_3237_, v_inst_3238_, v_inst_3239_, v_inst_3240_, v_inst_3241_, v_n_u2080_3242_, v_filter_3243_, v_view_x3f_3244_, v_toBind_3245_, v___f_3246_, v___f_3247_, v_a_3248_, v_x_3249_, v___y_3250_);
lean_dec(v_a_3248_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3255_, lean_object* v_n_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_inst_3262_, lean_object* v_n_u2080_3263_, lean_object* v_filter_3264_, lean_object* v_view_x3f_3265_, lean_object* v_toBind_3266_, lean_object* v___f_3267_, lean_object* v___f_3268_, lean_object* v___x_3269_, lean_object* v_____do__lift_3270_){
_start:
{
if (lean_obj_tag(v_____do__lift_3270_) == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v___x_3269_);
lean_dec(v___f_3268_);
lean_dec(v___f_3267_);
lean_dec(v_toBind_3266_);
lean_dec(v_view_x3f_3265_);
lean_dec(v_filter_3264_);
lean_dec(v_n_u2080_3263_);
lean_dec(v_inst_3262_);
lean_dec_ref(v_inst_3261_);
lean_dec(v_inst_3260_);
lean_dec_ref(v_inst_3259_);
lean_dec_ref(v_inst_3258_);
lean_dec_ref(v_inst_3257_);
lean_dec(v_n_3256_);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_apply_2(v_toPure_3255_, lean_box(0), v___x_3271_);
return v___x_3272_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3273_ = l_Lean_privateToUserName(v_n_3256_);
v___x_3274_ = l_Lean_Name_componentsRev(v___x_3273_);
v___x_3275_ = lean_box(0);
lean_inc(v_toPure_3255_);
v___f_3276_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3276_, 0, v_toPure_3255_);
lean_closure_set(v___f_3276_, 1, v___x_3275_);
lean_inc(v_toBind_3266_);
v___f_3277_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3277_, 0, v_toPure_3255_);
lean_closure_set(v___f_3277_, 1, v___x_3275_);
lean_closure_set(v___f_3277_, 2, v_inst_3257_);
lean_closure_set(v___f_3277_, 3, v_inst_3258_);
lean_closure_set(v___f_3277_, 4, v_inst_3259_);
lean_closure_set(v___f_3277_, 5, v_inst_3260_);
lean_closure_set(v___f_3277_, 6, v_inst_3261_);
lean_closure_set(v___f_3277_, 7, v_inst_3262_);
lean_closure_set(v___f_3277_, 8, v_n_u2080_3263_);
lean_closure_set(v___f_3277_, 9, v_filter_3264_);
lean_closure_set(v___f_3277_, 10, v_view_x3f_3265_);
lean_closure_set(v___f_3277_, 11, v_toBind_3266_);
lean_closure_set(v___f_3277_, 12, v___f_3267_);
lean_closure_set(v___f_3277_, 13, v___f_3268_);
v___x_3278_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3279_ = l_List_forIn_x27_loop___redArg(v___x_3269_, v___f_3277_, v___x_3274_, v___x_3278_);
v___x_3280_ = lean_apply_4(v_toBind_3266_, lean_box(0), lean_box(0), v___x_3279_, v___f_3276_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3281_, lean_object* v_n_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_n_u2080_3289_, lean_object* v_filter_3290_, lean_object* v_view_x3f_3291_, lean_object* v_toBind_3292_, lean_object* v___f_3293_, lean_object* v___f_3294_, lean_object* v___x_3295_, lean_object* v_____do__lift_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3281_, v_n_3282_, v_inst_3283_, v_inst_3284_, v_inst_3285_, v_inst_3286_, v_inst_3287_, v_inst_3288_, v_n_u2080_3289_, v_filter_3290_, v_view_x3f_3291_, v_toBind_3292_, v___f_3293_, v___f_3294_, v___x_3295_, v_____do__lift_3296_);
lean_dec(v_____do__lift_3296_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3298_, lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_n_u2080_3304_, lean_object* v_filter_3305_, lean_object* v_view_x3f_3306_, lean_object* v_n_3307_){
_start:
{
lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___f_3311_; lean_object* v___f_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___y_3319_; uint8_t v___x_3327_; 
lean_inc_ref(v_inst_3298_);
v___f_3308_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3308_, 0, v_inst_3298_);
lean_inc_ref(v_inst_3298_);
v___f_3309_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3309_, 0, v_inst_3298_);
lean_inc_ref(v_inst_3298_);
v___f_3310_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3310_, 0, v_inst_3298_);
lean_inc_ref(v_inst_3298_);
v___f_3311_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3311_, 0, v_inst_3298_);
lean_inc_ref(v_inst_3298_);
v___f_3312_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3312_, 0, v_inst_3298_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___f_3308_);
lean_ctor_set(v___x_3313_, 1, v___f_3309_);
lean_inc_ref(v_inst_3298_);
v___x_3314_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3314_, 0, lean_box(0));
lean_closure_set(v___x_3314_, 1, v_inst_3298_);
v___x_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
lean_ctor_set(v___x_3315_, 2, v___f_3310_);
lean_ctor_set(v___x_3315_, 3, v___f_3311_);
lean_ctor_set(v___x_3315_, 4, v___f_3312_);
lean_inc_ref(v_inst_3298_);
v___x_3316_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3316_, 0, lean_box(0));
lean_closure_set(v___x_3316_, 1, v_inst_3298_);
v___x_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3327_ = l_Lean_Name_hasMacroScopes(v_n_3307_);
if (v___x_3327_ == 0)
{
lean_object* v_toApplicative_3328_; lean_object* v_toPure_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_toApplicative_3328_ = lean_ctor_get(v_inst_3298_, 0);
v_toPure_3329_ = lean_ctor_get(v_toApplicative_3328_, 1);
v___x_3330_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3329_);
v___x_3331_ = lean_apply_2(v_toPure_3329_, lean_box(0), v___x_3330_);
v___y_3319_ = v___x_3331_;
goto v___jp_3318_;
}
else
{
lean_object* v_toApplicative_3332_; lean_object* v_toPure_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_toApplicative_3332_ = lean_ctor_get(v_inst_3298_, 0);
v_toPure_3333_ = lean_ctor_get(v_toApplicative_3332_, 1);
v___x_3334_ = lean_box(0);
lean_inc(v_toPure_3333_);
v___x_3335_ = lean_apply_2(v_toPure_3333_, lean_box(0), v___x_3334_);
v___y_3319_ = v___x_3335_;
goto v___jp_3318_;
}
v___jp_3318_:
{
lean_object* v_toApplicative_3320_; lean_object* v_toBind_3321_; lean_object* v_toPure_3322_; lean_object* v___f_3323_; lean_object* v___f_3324_; lean_object* v___f_3325_; lean_object* v___x_3326_; 
v_toApplicative_3320_ = lean_ctor_get(v_inst_3298_, 0);
v_toBind_3321_ = lean_ctor_get(v_inst_3298_, 1);
lean_inc(v_toBind_3321_);
v_toPure_3322_ = lean_ctor_get(v_toApplicative_3320_, 1);
lean_inc(v_toPure_3322_);
lean_inc(v_toPure_3322_);
v___f_3323_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3323_, 0, v_toPure_3322_);
lean_inc(v_toPure_3322_);
v___f_3324_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3324_, 0, v_toPure_3322_);
lean_inc(v_toBind_3321_);
v___f_3325_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3325_, 0, v_toPure_3322_);
lean_closure_set(v___f_3325_, 1, v_n_3307_);
lean_closure_set(v___f_3325_, 2, v_inst_3298_);
lean_closure_set(v___f_3325_, 3, v_inst_3299_);
lean_closure_set(v___f_3325_, 4, v_inst_3300_);
lean_closure_set(v___f_3325_, 5, v_inst_3301_);
lean_closure_set(v___f_3325_, 6, v_inst_3302_);
lean_closure_set(v___f_3325_, 7, v_inst_3303_);
lean_closure_set(v___f_3325_, 8, v_n_u2080_3304_);
lean_closure_set(v___f_3325_, 9, v_filter_3305_);
lean_closure_set(v___f_3325_, 10, v_view_x3f_3306_);
lean_closure_set(v___f_3325_, 11, v_toBind_3321_);
lean_closure_set(v___f_3325_, 12, v___f_3324_);
lean_closure_set(v___f_3325_, 13, v___f_3323_);
lean_closure_set(v___f_3325_, 14, v___x_3317_);
v___x_3326_ = lean_apply_4(v_toBind_3321_, lean_box(0), lean_box(0), v___y_3319_, v___f_3325_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_n_u2080_3343_, lean_object* v_filter_3344_, lean_object* v_view_x3f_3345_, lean_object* v_n_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3337_, v_inst_3338_, v_inst_3339_, v_inst_3340_, v_inst_3341_, v_inst_3342_, v_n_u2080_3343_, v_filter_3344_, v_view_x3f_3345_, v_n_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3348_, lean_object* v_x1_3349_, lean_object* v_x2_3350_){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; uint8_t v___x_3353_; 
v___x_3351_ = l_Lean_Name_getPrefix(v_x2_3350_);
v___x_3352_ = l_Lean_Name_getPrefix(v_n_u2081_3348_);
v___x_3353_ = l_Lean_Name_isPrefixOf(v___x_3351_, v___x_3352_);
lean_dec(v___x_3352_);
lean_dec(v___x_3351_);
if (v___x_3353_ == 0)
{
lean_dec(v_x2_3350_);
return v_x1_3349_;
}
else
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_array_push(v_x1_3349_, v_x2_3350_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3355_, lean_object* v_x1_3356_, lean_object* v_x2_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3355_, v_x1_3356_, v_x2_3357_);
lean_dec(v_n_u2081_3355_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3359_, lean_object* v_n_u2081_3360_, lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_n_u2080_3367_, lean_object* v_filter_3368_, lean_object* v_toPure_3369_, lean_object* v_____do__lift_3370_){
_start:
{
if (lean_obj_tag(v_____do__lift_3370_) == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec(v_toPure_3369_);
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v_view_3359_);
v___x_3372_ = l_Lean_rootNamespace;
v___x_3373_ = l_Lean_Name_append(v___x_3372_, v_n_u2081_3360_);
v___x_3374_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3361_, v_inst_3362_, v_inst_3363_, v_inst_3364_, v_inst_3365_, v_inst_3366_, v_n_u2080_3367_, v_filter_3368_, v___x_3371_, v___x_3373_);
return v___x_3374_;
}
else
{
lean_object* v___x_3375_; 
lean_dec(v_filter_3368_);
lean_dec(v_n_u2080_3367_);
lean_dec(v_inst_3366_);
lean_dec_ref(v_inst_3365_);
lean_dec(v_inst_3364_);
lean_dec_ref(v_inst_3363_);
lean_dec_ref(v_inst_3362_);
lean_dec_ref(v_inst_3361_);
lean_dec(v_n_u2081_3360_);
lean_dec_ref(v_view_3359_);
v___x_3375_ = lean_apply_2(v_toPure_3369_, lean_box(0), v_____do__lift_3370_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3376_, lean_object* v_inst_3377_, lean_object* v_inst_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_n_u2080_3383_, lean_object* v_filter_3384_, lean_object* v_toBind_3385_, lean_object* v___f_3386_, uint8_t v_allowHorizAliases_3387_, lean_object* v___f_3388_, lean_object* v_____do__lift_3389_){
_start:
{
lean_object* v_aliases_3391_; 
if (lean_obj_tag(v_____do__lift_3389_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_dec_ref(v___f_3388_);
lean_dec(v___f_3386_);
lean_dec(v_toBind_3385_);
lean_dec(v_filter_3384_);
lean_dec(v_n_u2080_3383_);
lean_dec(v_inst_3382_);
lean_dec_ref(v_inst_3381_);
lean_dec(v_inst_3380_);
lean_dec_ref(v_inst_3379_);
lean_dec_ref(v_inst_3378_);
lean_dec_ref(v_inst_3377_);
v___x_3398_ = lean_box(0);
v___x_3399_ = lean_apply_2(v_toPure_3376_, lean_box(0), v___x_3398_);
return v___x_3399_;
}
else
{
lean_object* v_val_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
lean_dec(v_toPure_3376_);
v_val_3400_ = lean_ctor_get(v_____do__lift_3389_, 0);
lean_inc(v_val_3400_);
lean_dec_ref(v_____do__lift_3389_);
lean_inc(v_n_u2080_3383_);
v___x_3401_ = l_Lean_getRevAliases(v_val_3400_, v_n_u2080_3383_);
v___x_3402_ = lean_array_mk(v___x_3401_);
if (v_allowHorizAliases_3387_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3403_ = lean_unsigned_to_nat(0u);
v___x_3404_ = lean_array_get_size(v___x_3402_);
v___x_3405_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3406_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3407_ = lean_nat_dec_lt(v___x_3403_, v___x_3404_);
if (v___x_3407_ == 0)
{
lean_dec_ref(v___x_3402_);
lean_dec_ref(v___f_3388_);
v_aliases_3391_ = v___x_3405_;
goto v___jp_3390_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_nat_dec_le(v___x_3404_, v___x_3404_);
if (v___x_3408_ == 0)
{
if (v___x_3407_ == 0)
{
lean_dec_ref(v___x_3402_);
lean_dec_ref(v___f_3388_);
v_aliases_3391_ = v___x_3405_;
goto v___jp_3390_;
}
else
{
size_t v___x_3409_; size_t v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = ((size_t)0ULL);
v___x_3410_ = lean_usize_of_nat(v___x_3404_);
v___x_3411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3406_, v___f_3388_, v___x_3402_, v___x_3409_, v___x_3410_, v___x_3405_);
v_aliases_3391_ = v___x_3411_;
goto v___jp_3390_;
}
}
else
{
size_t v___x_3412_; size_t v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = ((size_t)0ULL);
v___x_3413_ = lean_usize_of_nat(v___x_3404_);
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3406_, v___f_3388_, v___x_3402_, v___x_3412_, v___x_3413_, v___x_3405_);
v_aliases_3391_ = v___x_3414_;
goto v___jp_3390_;
}
}
}
else
{
lean_dec_ref(v___f_3388_);
v_aliases_3391_ = v___x_3402_;
goto v___jp_3390_;
}
}
v___jp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_inc_ref(v_inst_3377_);
v___x_3392_ = l_OptionT_instAlternative___redArg(v_inst_3377_);
v___x_3393_ = lean_box(0);
v___x_3394_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3394_, 0, lean_box(0));
lean_closure_set(v___x_3394_, 1, v_inst_3377_);
lean_closure_set(v___x_3394_, 2, v_inst_3378_);
lean_closure_set(v___x_3394_, 3, v_inst_3379_);
lean_closure_set(v___x_3394_, 4, v_inst_3380_);
lean_closure_set(v___x_3394_, 5, v_inst_3381_);
lean_closure_set(v___x_3394_, 6, v_inst_3382_);
lean_closure_set(v___x_3394_, 7, v_n_u2080_3383_);
lean_closure_set(v___x_3394_, 8, v_filter_3384_);
lean_closure_set(v___x_3394_, 9, v___x_3393_);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3392_, v___x_3394_, v_aliases_3391_, v___x_3395_);
v___x_3397_ = lean_apply_4(v_toBind_3385_, lean_box(0), lean_box(0), v___x_3396_, v___f_3386_);
return v___x_3397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3415_, lean_object* v_inst_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_n_u2080_3422_, lean_object* v_filter_3423_, lean_object* v_toBind_3424_, lean_object* v___f_3425_, lean_object* v_allowHorizAliases_3426_, lean_object* v___f_3427_, lean_object* v_____do__lift_3428_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3429_; lean_object* v_res_3430_; 
v_allowHorizAliases_boxed_3429_ = lean_unbox(v_allowHorizAliases_3426_);
v_res_3430_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3415_, v_inst_3416_, v_inst_3417_, v_inst_3418_, v_inst_3419_, v_inst_3420_, v_inst_3421_, v_n_u2080_3422_, v_filter_3423_, v_toBind_3424_, v___f_3425_, v_allowHorizAliases_boxed_3429_, v___f_3427_, v_____do__lift_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3431_, lean_object* v_____do__lift_3432_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_____do__lift_3432_);
v___x_3434_ = lean_apply_2(v_toPure_3431_, lean_box(0), v___x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3435_, lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_inst_3441_, lean_object* v_n_u2080_3442_, lean_object* v_filter_3443_, lean_object* v___x_3444_, lean_object* v_toPure_3445_, lean_object* v_____do__lift_3446_){
_start:
{
if (lean_obj_tag(v_____do__lift_3446_) == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec(v_toPure_3445_);
v___x_3447_ = l_Lean_rootNamespace;
v___x_3448_ = l_Lean_Name_append(v___x_3447_, v_n_u2081_3435_);
v___x_3449_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3436_, v_inst_3437_, v_inst_3438_, v_inst_3439_, v_inst_3440_, v_inst_3441_, v_n_u2080_3442_, v_filter_3443_, v___x_3444_, v___x_3448_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; 
lean_dec(v___x_3444_);
lean_dec(v_filter_3443_);
lean_dec(v_n_u2080_3442_);
lean_dec(v_inst_3441_);
lean_dec_ref(v_inst_3440_);
lean_dec(v_inst_3439_);
lean_dec_ref(v_inst_3438_);
lean_dec_ref(v_inst_3437_);
lean_dec_ref(v_inst_3436_);
lean_dec(v_n_u2081_3435_);
v___x_3450_ = lean_apply_2(v_toPure_3445_, lean_box(0), v_____do__lift_3446_);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_inst_3455_, lean_object* v_inst_3456_, lean_object* v_n_u2080_3457_, uint8_t v_fullNames_3458_, uint8_t v_allowHorizAliases_3459_, lean_object* v_filter_3460_){
_start:
{
lean_object* v_view_3461_; lean_object* v_name_3462_; lean_object* v_n_u2081_3463_; 
lean_inc(v_n_u2080_3457_);
v_view_3461_ = l_Lean_extractMacroScopes(v_n_u2080_3457_);
v_name_3462_ = lean_ctor_get(v_view_3461_, 0);
lean_inc(v_name_3462_);
v_n_u2081_3463_ = l_Lean_privateToUserName(v_name_3462_);
if (v_fullNames_3458_ == 0)
{
lean_object* v_toApplicative_3464_; lean_object* v_getEnv_3465_; lean_object* v_toBind_3466_; lean_object* v_toPure_3467_; lean_object* v___f_3468_; lean_object* v___f_3469_; lean_object* v___x_3470_; lean_object* v___f_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_toApplicative_3464_ = lean_ctor_get(v_inst_3451_, 0);
v_getEnv_3465_ = lean_ctor_get(v_inst_3453_, 0);
lean_inc(v_getEnv_3465_);
v_toBind_3466_ = lean_ctor_get(v_inst_3451_, 1);
lean_inc(v_toBind_3466_);
v_toPure_3467_ = lean_ctor_get(v_toApplicative_3464_, 1);
lean_inc(v_toPure_3467_);
lean_inc(v_n_u2081_3463_);
v___f_3468_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3468_, 0, v_n_u2081_3463_);
lean_inc(v_toPure_3467_);
lean_inc(v_filter_3460_);
lean_inc(v_n_u2080_3457_);
lean_inc(v_inst_3456_);
lean_inc_ref(v_inst_3455_);
lean_inc(v_inst_3454_);
lean_inc_ref(v_inst_3453_);
lean_inc_ref(v_inst_3452_);
lean_inc_ref(v_inst_3451_);
v___f_3469_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3469_, 0, v_view_3461_);
lean_closure_set(v___f_3469_, 1, v_n_u2081_3463_);
lean_closure_set(v___f_3469_, 2, v_inst_3451_);
lean_closure_set(v___f_3469_, 3, v_inst_3452_);
lean_closure_set(v___f_3469_, 4, v_inst_3453_);
lean_closure_set(v___f_3469_, 5, v_inst_3454_);
lean_closure_set(v___f_3469_, 6, v_inst_3455_);
lean_closure_set(v___f_3469_, 7, v_inst_3456_);
lean_closure_set(v___f_3469_, 8, v_n_u2080_3457_);
lean_closure_set(v___f_3469_, 9, v_filter_3460_);
lean_closure_set(v___f_3469_, 10, v_toPure_3467_);
v___x_3470_ = lean_box(v_allowHorizAliases_3459_);
lean_inc(v_toBind_3466_);
lean_inc(v_toPure_3467_);
v___f_3471_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_3471_, 0, v_toPure_3467_);
lean_closure_set(v___f_3471_, 1, v_inst_3451_);
lean_closure_set(v___f_3471_, 2, v_inst_3452_);
lean_closure_set(v___f_3471_, 3, v_inst_3453_);
lean_closure_set(v___f_3471_, 4, v_inst_3454_);
lean_closure_set(v___f_3471_, 5, v_inst_3455_);
lean_closure_set(v___f_3471_, 6, v_inst_3456_);
lean_closure_set(v___f_3471_, 7, v_n_u2080_3457_);
lean_closure_set(v___f_3471_, 8, v_filter_3460_);
lean_closure_set(v___f_3471_, 9, v_toBind_3466_);
lean_closure_set(v___f_3471_, 10, v___f_3469_);
lean_closure_set(v___f_3471_, 11, v___x_3470_);
lean_closure_set(v___f_3471_, 12, v___f_3468_);
v___f_3472_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3472_, 0, v_toPure_3467_);
lean_inc(v_toBind_3466_);
v___x_3473_ = lean_apply_4(v_toBind_3466_, lean_box(0), lean_box(0), v_getEnv_3465_, v___f_3472_);
v___x_3474_ = lean_apply_4(v_toBind_3466_, lean_box(0), lean_box(0), v___x_3473_, v___f_3471_);
return v___x_3474_;
}
else
{
lean_object* v_toApplicative_3475_; lean_object* v_toBind_3476_; lean_object* v_toPure_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; 
v_toApplicative_3475_ = lean_ctor_get(v_inst_3451_, 0);
v_toBind_3476_ = lean_ctor_get(v_inst_3451_, 1);
lean_inc(v_toBind_3476_);
v_toPure_3477_ = lean_ctor_get(v_toApplicative_3475_, 1);
lean_inc(v_toPure_3477_);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_view_3461_);
lean_inc(v_n_u2081_3463_);
lean_inc_ref(v___x_3478_);
lean_inc(v_filter_3460_);
lean_inc(v_n_u2080_3457_);
lean_inc(v_inst_3456_);
lean_inc_ref(v_inst_3455_);
lean_inc(v_inst_3454_);
lean_inc_ref(v_inst_3453_);
lean_inc_ref(v_inst_3452_);
lean_inc_ref(v_inst_3451_);
v___x_3479_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3451_, v_inst_3452_, v_inst_3453_, v_inst_3454_, v_inst_3455_, v_inst_3456_, v_n_u2080_3457_, v_filter_3460_, v___x_3478_, v_n_u2081_3463_);
v___f_3480_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3480_, 0, v_n_u2081_3463_);
lean_closure_set(v___f_3480_, 1, v_inst_3451_);
lean_closure_set(v___f_3480_, 2, v_inst_3452_);
lean_closure_set(v___f_3480_, 3, v_inst_3453_);
lean_closure_set(v___f_3480_, 4, v_inst_3454_);
lean_closure_set(v___f_3480_, 5, v_inst_3455_);
lean_closure_set(v___f_3480_, 6, v_inst_3456_);
lean_closure_set(v___f_3480_, 7, v_n_u2080_3457_);
lean_closure_set(v___f_3480_, 8, v_filter_3460_);
lean_closure_set(v___f_3480_, 9, v___x_3478_);
lean_closure_set(v___f_3480_, 10, v_toPure_3477_);
v___x_3481_ = lean_apply_4(v_toBind_3476_, lean_box(0), lean_box(0), v___x_3479_, v___f_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_inst_3486_, lean_object* v_inst_3487_, lean_object* v_n_u2080_3488_, lean_object* v_fullNames_3489_, lean_object* v_allowHorizAliases_3490_, lean_object* v_filter_3491_){
_start:
{
uint8_t v_fullNames_boxed_3492_; uint8_t v_allowHorizAliases_boxed_3493_; lean_object* v_res_3494_; 
v_fullNames_boxed_3492_ = lean_unbox(v_fullNames_3489_);
v_allowHorizAliases_boxed_3493_ = lean_unbox(v_allowHorizAliases_3490_);
v_res_3494_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3482_, v_inst_3483_, v_inst_3484_, v_inst_3485_, v_inst_3486_, v_inst_3487_, v_n_u2080_3488_, v_fullNames_boxed_3492_, v_allowHorizAliases_boxed_3493_, v_filter_3491_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_, lean_object* v_inst_3501_, lean_object* v_n_u2080_3502_, uint8_t v_fullNames_3503_, uint8_t v_allowHorizAliases_3504_, lean_object* v_filter_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3496_, v_inst_3497_, v_inst_3498_, v_inst_3499_, v_inst_3500_, v_inst_3501_, v_n_u2080_3502_, v_fullNames_3503_, v_allowHorizAliases_3504_, v_filter_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3507_, lean_object* v_inst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_n_u2080_3514_, lean_object* v_fullNames_3515_, lean_object* v_allowHorizAliases_3516_, lean_object* v_filter_3517_){
_start:
{
uint8_t v_fullNames_boxed_3518_; uint8_t v_allowHorizAliases_boxed_3519_; lean_object* v_res_3520_; 
v_fullNames_boxed_3518_ = lean_unbox(v_fullNames_3515_);
v_allowHorizAliases_boxed_3519_ = lean_unbox(v_allowHorizAliases_3516_);
v_res_3520_ = l_Lean_unresolveNameGlobal_x3f(v_m_3507_, v_inst_3508_, v_inst_3509_, v_inst_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_n_u2080_3514_, v_fullNames_boxed_3518_, v_allowHorizAliases_boxed_3519_, v_filter_3517_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3521_, lean_object* v_n_u2080_3522_, lean_object* v_n_x3f_3523_){
_start:
{
if (lean_obj_tag(v_n_x3f_3523_) == 0)
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_apply_2(v_toPure_3521_, lean_box(0), v_n_u2080_3522_);
return v___x_3524_;
}
else
{
lean_object* v_val_3525_; lean_object* v___x_3526_; 
lean_dec(v_n_u2080_3522_);
v_val_3525_ = lean_ctor_get(v_n_x3f_3523_, 0);
lean_inc(v_val_3525_);
lean_dec_ref(v_n_x3f_3523_);
v___x_3526_ = lean_apply_2(v_toPure_3521_, lean_box(0), v_val_3525_);
return v___x_3526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_n_u2080_3533_, uint8_t v_fullNames_3534_, uint8_t v_allowHorizAliases_3535_, lean_object* v_filter_3536_){
_start:
{
lean_object* v_toApplicative_3537_; lean_object* v_toBind_3538_; lean_object* v_toPure_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v___x_3542_; 
v_toApplicative_3537_ = lean_ctor_get(v_inst_3527_, 0);
v_toBind_3538_ = lean_ctor_get(v_inst_3527_, 1);
lean_inc(v_toBind_3538_);
v_toPure_3539_ = lean_ctor_get(v_toApplicative_3537_, 1);
lean_inc(v_toPure_3539_);
lean_inc(v_n_u2080_3533_);
v___x_3540_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3527_, v_inst_3528_, v_inst_3529_, v_inst_3530_, v_inst_3531_, v_inst_3532_, v_n_u2080_3533_, v_fullNames_3534_, v_allowHorizAliases_3535_, v_filter_3536_);
v___f_3541_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3541_, 0, v_toPure_3539_);
lean_closure_set(v___f_3541_, 1, v_n_u2080_3533_);
v___x_3542_ = lean_apply_4(v_toBind_3538_, lean_box(0), lean_box(0), v___x_3540_, v___f_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3543_, lean_object* v_inst_3544_, lean_object* v_inst_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, lean_object* v_inst_3548_, lean_object* v_n_u2080_3549_, lean_object* v_fullNames_3550_, lean_object* v_allowHorizAliases_3551_, lean_object* v_filter_3552_){
_start:
{
uint8_t v_fullNames_boxed_3553_; uint8_t v_allowHorizAliases_boxed_3554_; lean_object* v_res_3555_; 
v_fullNames_boxed_3553_ = lean_unbox(v_fullNames_3550_);
v_allowHorizAliases_boxed_3554_ = lean_unbox(v_allowHorizAliases_3551_);
v_res_3555_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3543_, v_inst_3544_, v_inst_3545_, v_inst_3546_, v_inst_3547_, v_inst_3548_, v_n_u2080_3549_, v_fullNames_boxed_3553_, v_allowHorizAliases_boxed_3554_, v_filter_3552_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3556_, lean_object* v_inst_3557_, lean_object* v_inst_3558_, lean_object* v_inst_3559_, lean_object* v_inst_3560_, lean_object* v_inst_3561_, lean_object* v_inst_3562_, lean_object* v_n_u2080_3563_, uint8_t v_fullNames_3564_, uint8_t v_allowHorizAliases_3565_, lean_object* v_filter_3566_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3557_, v_inst_3558_, v_inst_3559_, v_inst_3560_, v_inst_3561_, v_inst_3562_, v_n_u2080_3563_, v_fullNames_3564_, v_allowHorizAliases_3565_, v_filter_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_, lean_object* v_n_u2080_3575_, lean_object* v_fullNames_3576_, lean_object* v_allowHorizAliases_3577_, lean_object* v_filter_3578_){
_start:
{
uint8_t v_fullNames_boxed_3579_; uint8_t v_allowHorizAliases_boxed_3580_; lean_object* v_res_3581_; 
v_fullNames_boxed_3579_ = lean_unbox(v_fullNames_3576_);
v_allowHorizAliases_boxed_3580_ = lean_unbox(v_allowHorizAliases_3577_);
v_res_3581_ = l_Lean_unresolveNameGlobal(v_m_3568_, v_inst_3569_, v_inst_3570_, v_inst_3571_, v_inst_3572_, v_inst_3573_, v_inst_3574_, v_n_u2080_3575_, v_fullNames_boxed_3579_, v_allowHorizAliases_boxed_3580_, v_filter_3578_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_n_3591_){
_start:
{
lean_object* v_map_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_map_3592_ = lean_ctor_get(v_toFunctor_3583_, 0);
lean_inc(v_map_3592_);
lean_dec_ref(v_toFunctor_3583_);
v___x_3593_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3594_ = l_Lean_resolveLocalName___redArg(v_inst_3584_, v_inst_3585_, v_inst_3586_, v_inst_3587_, v_inst_3588_, v_inst_3589_, v_inst_3590_, v_n_3591_);
v___x_3595_ = lean_apply_4(v_map_3592_, lean_box(0), lean_box(0), v___x_3593_, v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_n_u2080_3603_, uint8_t v_fullNames_3604_){
_start:
{
lean_object* v_toApplicative_3605_; lean_object* v_toFunctor_3606_; uint8_t v___x_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; 
v_toApplicative_3605_ = lean_ctor_get(v_inst_3596_, 0);
v_toFunctor_3606_ = lean_ctor_get(v_toApplicative_3605_, 0);
v___x_3607_ = 0;
lean_inc(v_inst_3601_);
lean_inc_ref(v_inst_3600_);
lean_inc(v_inst_3599_);
lean_inc_ref(v_inst_3598_);
lean_inc_ref(v_inst_3597_);
lean_inc_ref(v_inst_3596_);
lean_inc_ref(v_toFunctor_3606_);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3608_, 0, v_toFunctor_3606_);
lean_closure_set(v___f_3608_, 1, v_inst_3596_);
lean_closure_set(v___f_3608_, 2, v_inst_3597_);
lean_closure_set(v___f_3608_, 3, v_inst_3598_);
lean_closure_set(v___f_3608_, 4, v_inst_3599_);
lean_closure_set(v___f_3608_, 5, v_inst_3600_);
lean_closure_set(v___f_3608_, 6, v_inst_3601_);
lean_closure_set(v___f_3608_, 7, v_inst_3602_);
v___x_3609_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_n_u2080_3603_, v_fullNames_3604_, v___x_3607_, v___f_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_n_u2080_3617_, lean_object* v_fullNames_3618_){
_start:
{
uint8_t v_fullNames_boxed_3619_; lean_object* v_res_3620_; 
v_fullNames_boxed_3619_ = lean_unbox(v_fullNames_3618_);
v_res_3620_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_inst_3616_, v_n_u2080_3617_, v_fullNames_boxed_3619_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3621_, lean_object* v_inst_3622_, lean_object* v_inst_3623_, lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_n_u2080_3629_, uint8_t v_fullNames_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3622_, v_inst_3623_, v_inst_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_n_u2080_3629_, v_fullNames_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_n_u2080_3640_, lean_object* v_fullNames_3641_){
_start:
{
uint8_t v_fullNames_boxed_3642_; lean_object* v_res_3643_; 
v_fullNames_boxed_3642_ = lean_unbox(v_fullNames_3641_);
v_res_3643_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3632_, v_inst_3633_, v_inst_3634_, v_inst_3635_, v_inst_3636_, v_inst_3637_, v_inst_3638_, v_inst_3639_, v_n_u2080_3640_, v_fullNames_boxed_3642_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3644_, lean_object* v_inst_3645_, lean_object* v_inst_3646_, lean_object* v_inst_3647_, lean_object* v_inst_3648_, lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_n_u2080_3651_, uint8_t v_fullNames_3652_){
_start:
{
lean_object* v_toApplicative_3653_; lean_object* v_toBind_3654_; lean_object* v_toPure_3655_; lean_object* v___x_3656_; lean_object* v___f_3657_; lean_object* v___x_3658_; 
v_toApplicative_3653_ = lean_ctor_get(v_inst_3644_, 0);
v_toBind_3654_ = lean_ctor_get(v_inst_3644_, 1);
lean_inc(v_toBind_3654_);
v_toPure_3655_ = lean_ctor_get(v_toApplicative_3653_, 1);
lean_inc(v_toPure_3655_);
lean_inc(v_n_u2080_3651_);
v___x_3656_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3644_, v_inst_3645_, v_inst_3646_, v_inst_3647_, v_inst_3648_, v_inst_3649_, v_inst_3650_, v_n_u2080_3651_, v_fullNames_3652_);
v___f_3657_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3657_, 0, v_toPure_3655_);
lean_closure_set(v___f_3657_, 1, v_n_u2080_3651_);
v___x_3658_ = lean_apply_4(v_toBind_3654_, lean_box(0), lean_box(0), v___x_3656_, v___f_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_n_u2080_3666_, lean_object* v_fullNames_3667_){
_start:
{
uint8_t v_fullNames_boxed_3668_; lean_object* v_res_3669_; 
v_fullNames_boxed_3668_ = lean_unbox(v_fullNames_3667_);
v_res_3669_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3659_, v_inst_3660_, v_inst_3661_, v_inst_3662_, v_inst_3663_, v_inst_3664_, v_inst_3665_, v_n_u2080_3666_, v_fullNames_boxed_3668_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3670_, lean_object* v_inst_3671_, lean_object* v_inst_3672_, lean_object* v_inst_3673_, lean_object* v_inst_3674_, lean_object* v_inst_3675_, lean_object* v_inst_3676_, lean_object* v_inst_3677_, lean_object* v_n_u2080_3678_, uint8_t v_fullNames_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3671_, v_inst_3672_, v_inst_3673_, v_inst_3674_, v_inst_3675_, v_inst_3676_, v_inst_3677_, v_n_u2080_3678_, v_fullNames_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_inst_3687_, lean_object* v_inst_3688_, lean_object* v_n_u2080_3689_, lean_object* v_fullNames_3690_){
_start:
{
uint8_t v_fullNames_boxed_3691_; lean_object* v_res_3692_; 
v_fullNames_boxed_3691_ = lean_unbox(v_fullNames_3690_);
v_res_3692_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3681_, v_inst_3682_, v_inst_3683_, v_inst_3684_, v_inst_3685_, v_inst_3686_, v_inst_3687_, v_inst_3688_, v_n_u2080_3689_, v_fullNames_boxed_3691_);
return v_res_3692_;
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
res = l_Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesRef);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesExt);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_aliasExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_aliasExtension);
lean_dec_ref(res);
res = l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ResolveName_backward_privateInPublic = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ResolveName_backward_privateInPublic);
lean_dec_ref(res);
res = l_Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
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
