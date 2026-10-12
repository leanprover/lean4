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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Array_instInhabited___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "reservedNamePredicatesExt"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 132, 75, 91, 63, 63, 128, 135)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "aliasExtension"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 78, 120, 122, 20, 252, 110, 252)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addAliasEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_aliasExtension;
LEAN_EXPORT lean_object* l_Lean_addAlias___lam__0(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_68_;
v_res_68_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2____boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
return v_res_70_;
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_Lean_registerReservedNamePredicate___closed__0));
v___x_73_ = lean_mk_io_user_error(v___x_72_);
return v___x_73_;
}
}
lean_object* l_Lean_registerReservedNamePredicate(lean_object* v_p_74_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_initializing();
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec_ref(v_p_74_);
v___x_77_ = lean_obj_once(&l_Lean_registerReservedNamePredicate___closed__1, &l_Lean_registerReservedNamePredicate___closed__1_once, _init_l_Lean_registerReservedNamePredicate___closed__1);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = l_Lean_reservedNamePredicatesRef;
v___x_80_ = lean_st_ref_take(v___x_79_);
v___x_81_ = lean_array_push(v___x_80_, v_p_74_);
v___x_82_ = lean_st_ref_put(v___x_79_, v___x_81_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT void l_Lean_registerReservedNamePredicate_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_74_ = stack[0].m_obj;
lean_object* v_res_84_;
v_res_84_ = l_Lean_registerReservedNamePredicate(v_p_74_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object* v_p_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_registerReservedNamePredicate(v_p_85_);
return v_res_87_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(lean_object* v___x_88_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_st_ref_get(v___x_88_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_88_ = stack[0].m_obj;
lean_object* v_res_92_;
v_res_92_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(v___x_88_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object* v___x_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(v___x_93_);
lean_dec(v___x_93_);
return v_res_95_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; 
v___x_96_ = l_Lean_reservedNamePredicatesRef;
v___f_97_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
return v___f_97_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; 
v___f_104_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_box(2);
v___x_107_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_));
v___x_108_ = 0;
v___x_109_ = 1;
v___x_110_ = l_Lean_registerEnvExtension___redArg(v___f_104_, v___x_105_, v___x_106_, v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_111_;
v_res_111_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
return v_res_113_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_env_114_, lean_object* v_name_115_, lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_154__overap_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_154__overap_120_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
lean_inc(v___x_154__overap_120_);
lean_inc(v_name_115_);
lean_inc_ref(v_env_114_);
v___x_121_ = lean_apply_2(v___x_154__overap_120_, v_env_114_, v_name_115_);
v___x_122_ = lean_unbox(v___x_121_);
if (v___x_122_ == 0)
{
size_t v___x_123_; size_t v___x_124_; 
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_i_117_, v___x_123_);
v_i_117_ = v___x_124_;
goto _start;
}
else
{
uint8_t v___x_126_; 
lean_dec(v_name_115_);
lean_dec_ref(v_env_114_);
v___x_126_ = lean_unbox(v___x_121_);
return v___x_126_;
}
}
else
{
uint8_t v___x_127_; 
lean_dec(v_name_115_);
lean_dec_ref(v_env_114_);
v___x_127_ = 0;
return v___x_127_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_114_ = stack[0].m_obj;
lean_object* v_name_115_ = stack[1].m_obj;
lean_object* v_as_116_ = stack[2].m_obj;
size_t v_i_117_ = stack[3].m_num;
size_t v_stop_118_ = stack[4].m_num;
uint8_t v_res_128_;
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_114_, v_name_115_, v_as_116_, v_i_117_, v_stop_118_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_env_129_, lean_object* v_name_130_, lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_stop_133_){
_start:
{
size_t v_i_boxed_134_; size_t v_stop_boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_i_boxed_134_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_stop_boxed_135_ = lean_unbox_usize(v_stop_133_);
lean_dec(v_stop_133_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_129_, v_name_130_, v_as_131_, v_i_boxed_134_, v_stop_boxed_135_);
lean_dec_ref(v_as_131_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Array_instInhabited___redArg();
return v___x_138_;
}
}
uint8_t lean_is_reserved_name(lean_object* v_env_139_, lean_object* v_name_140_){
_start:
{
lean_object* v___x_141_; lean_object* v_asyncMode_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_141_ = l_Lean_reservedNamePredicatesExt;
v_asyncMode_142_ = lean_ctor_get(v___x_141_, 2);
v___x_143_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_144_ = lean_box(0);
v___x_145_ = 0;
lean_inc_ref(v_env_139_);
v___x_146_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_143_, v___x_141_, v_env_139_, v_asyncMode_142_, v___x_144_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_array_get_size(v___x_146_);
v___x_149_ = lean_nat_dec_lt(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_dec(v___x_146_);
lean_dec(v_name_140_);
lean_dec_ref(v_env_139_);
return v___x_149_;
}
else
{
if (v___x_149_ == 0)
{
lean_dec(v___x_146_);
lean_dec(v_name_140_);
lean_dec_ref(v_env_139_);
return v___x_149_;
}
else
{
size_t v___x_150_; size_t v___x_151_; uint8_t v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_148_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_139_, v_name_140_, v___x_146_, v___x_150_, v___x_151_);
lean_dec(v___x_146_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT void lean_is_reserved_name_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_139_ = stack[0].m_obj;
lean_object* v_name_140_ = stack[1].m_obj;
uint8_t v_res_153_;
v_res_153_ = lean_is_reserved_name(v_env_139_, v_name_140_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_154_, lean_object* v_name_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = lean_is_reserved_name(v_env_154_, v_name_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_ks_162_; lean_object* v_vs_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_187_; 
v_ks_162_ = lean_ctor_get(v_x_158_, 0);
v_vs_163_ = lean_ctor_get(v_x_158_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_187_ == 0)
{
v___x_165_ = v_x_158_;
v_isShared_166_ = v_isSharedCheck_187_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_vs_163_);
lean_inc(v_ks_162_);
lean_dec(v_x_158_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_187_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_array_get_size(v_ks_162_);
v___x_168_ = lean_nat_dec_lt(v_x_159_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
lean_dec(v_x_159_);
v___x_169_ = lean_array_push(v_ks_162_, v_x_160_);
v___x_170_ = lean_array_push(v_vs_163_, v_x_161_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_170_);
lean_ctor_set(v___x_165_, 0, v___x_169_);
v___x_172_ = v___x_165_;
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
else
{
lean_object* v_k_x27_174_; uint8_t v___x_175_; 
v_k_x27_174_ = lean_array_fget_borrowed(v_ks_162_, v_x_159_);
v___x_175_ = lean_name_eq(v_x_160_, v_k_x27_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_177_; 
if (v_isShared_166_ == 0)
{
v___x_177_ = v___x_165_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_ks_162_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_vs_163_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_x_159_, v___x_178_);
lean_dec(v_x_159_);
v_x_158_ = v___x_177_;
v_x_159_ = v___x_179_;
goto _start;
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_array_fset(v_ks_162_, v_x_159_, v_x_160_);
v___x_183_ = lean_array_fset(v_vs_163_, v_x_159_, v_x_161_);
lean_dec(v_x_159_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_183_);
lean_ctor_set(v___x_165_, 0, v___x_182_);
v___x_185_ = v___x_165_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_188_, lean_object* v_k_189_, lean_object* v_v_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_188_, v___x_191_, v_k_189_, v_v_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_193_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_194_, size_t v_x_195_, size_t v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v_es_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v_j_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_es_199_ = lean_ctor_get(v_x_194_, 0);
v___x_200_ = ((size_t)31ULL);
v___x_201_ = lean_usize_land(v_x_195_, v___x_200_);
v_j_202_ = lean_usize_to_nat(v___x_201_);
v___x_203_ = lean_array_get_size(v_es_199_);
v___x_204_ = lean_nat_dec_lt(v_j_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_j_202_);
lean_dec(v_x_198_);
lean_dec(v_x_197_);
return v_x_194_;
}
else
{
lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_243_; 
lean_inc_ref(v_es_199_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_x_194_, 0);
lean_dec(v_unused_244_);
v___x_206_ = v_x_194_;
v_isShared_207_ = v_isSharedCheck_243_;
goto v_resetjp_205_;
}
else
{
lean_dec(v_x_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_243_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_v_208_; lean_object* v___x_209_; lean_object* v_xs_x27_210_; lean_object* v___y_212_; 
v_v_208_ = lean_array_fget(v_es_199_, v_j_202_);
v___x_209_ = lean_box(0);
v_xs_x27_210_ = lean_array_fset(v_es_199_, v_j_202_, v___x_209_);
switch(lean_obj_tag(v_v_208_))
{
case 0:
{
lean_object* v_key_217_; lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_228_; 
v_key_217_ = lean_ctor_get(v_v_208_, 0);
v_val_218_ = lean_ctor_get(v_v_208_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_v_208_);
if (v_isSharedCheck_228_ == 0)
{
v___x_220_ = v_v_208_;
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_inc(v_key_217_);
lean_dec(v_v_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; 
v___x_222_ = lean_name_eq(v_x_197_, v_key_217_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_del_object(v___x_220_);
v___x_223_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_217_, v_val_218_, v_x_197_, v_x_198_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___y_212_ = v___x_224_;
goto v___jp_211_;
}
else
{
lean_object* v___x_226_; 
lean_dec(v_val_218_);
lean_dec(v_key_217_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_x_198_);
lean_ctor_set(v___x_220_, 0, v_x_197_);
v___x_226_ = v___x_220_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_x_197_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_x_198_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
v___y_212_ = v___x_226_;
goto v___jp_211_;
}
}
}
}
case 1:
{
lean_object* v_node_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_241_; 
v_node_229_ = lean_ctor_get(v_v_208_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_v_208_);
if (v_isSharedCheck_241_ == 0)
{
v___x_231_ = v_v_208_;
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_node_229_);
lean_dec(v_v_208_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_233_ = ((size_t)5ULL);
v___x_234_ = lean_usize_shift_right(v_x_195_, v___x_233_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_x_196_, v___x_235_);
v___x_237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_229_, v___x_234_, v___x_236_, v_x_197_, v_x_198_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_237_);
v___x_239_ = v___x_231_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v___y_212_ = v___x_239_;
goto v___jp_211_;
}
}
}
default: 
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_x_197_);
lean_ctor_set(v___x_242_, 1, v_x_198_);
v___y_212_ = v___x_242_;
goto v___jp_211_;
}
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_array_fset(v_xs_x27_210_, v_j_202_, v___y_212_);
lean_dec(v_j_202_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_213_);
v___x_215_ = v___x_206_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
else
{
lean_object* v_ks_245_; lean_object* v_vs_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_264_; 
v_ks_245_ = lean_ctor_get(v_x_194_, 0);
v_vs_246_ = lean_ctor_get(v_x_194_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_264_ == 0)
{
v___x_248_ = v_x_194_;
v_isShared_249_ = v_isSharedCheck_264_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_vs_246_);
lean_inc(v_ks_245_);
lean_dec(v_x_194_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_264_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_ks_245_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_vs_246_);
v___x_251_ = v_reuseFailAlloc_263_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v_newNode_252_; size_t v___x_253_; uint8_t v___x_254_; 
v_newNode_252_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_251_, v_x_197_, v_x_198_);
v___x_253_ = ((size_t)7ULL);
v___x_254_ = lean_usize_dec_le(v___x_253_, v_x_196_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_252_);
v___x_256_ = lean_unsigned_to_nat(4u);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v_ks_258_; lean_object* v_vs_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_ks_258_ = lean_ctor_get(v_newNode_252_, 0);
lean_inc_ref(v_ks_258_);
v_vs_259_ = lean_ctor_get(v_newNode_252_, 1);
lean_inc_ref(v_vs_259_);
lean_dec_ref(v_newNode_252_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_262_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_196_, v_ks_258_, v_vs_259_, v___x_260_, v___x_261_);
lean_dec_ref(v_vs_259_);
lean_dec_ref(v_ks_258_);
return v___x_262_;
}
else
{
return v_newNode_252_;
}
}
else
{
return v_newNode_252_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_194_ = stack[0].m_obj;
size_t v_x_195_ = stack[1].m_num;
size_t v_x_196_ = stack[2].m_num;
lean_object* v_x_197_ = stack[3].m_obj;
lean_object* v_x_198_ = stack[4].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_194_, v_x_195_, v_x_196_, v_x_197_, v_x_198_);
stack->m_obj
 = v_res_265_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_266_, lean_object* v_keys_267_, lean_object* v_vals_268_, lean_object* v_i_269_, lean_object* v_entries_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_array_get_size(v_keys_267_);
v___x_272_ = lean_nat_dec_lt(v_i_269_, v___x_271_);
if (v___x_272_ == 0)
{
lean_dec(v_i_269_);
return v_entries_270_;
}
else
{
lean_object* v_k_273_; lean_object* v_v_274_; uint64_t v___y_276_; 
v_k_273_ = lean_array_fget_borrowed(v_keys_267_, v_i_269_);
v_v_274_ = lean_array_fget_borrowed(v_vals_268_, v_i_269_);
if (lean_obj_tag(v_k_273_) == 0)
{
uint64_t v___x_287_; 
v___x_287_ = 1723ULL;
v___y_276_ = v___x_287_;
goto v___jp_275_;
}
else
{
uint64_t v_hash_288_; 
v_hash_288_ = lean_ctor_get_uint64(v_k_273_, sizeof(void*)*2);
v___y_276_ = v_hash_288_;
goto v___jp_275_;
}
v___jp_275_:
{
size_t v_h_277_; size_t v___x_278_; lean_object* v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v_h_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_h_277_ = lean_uint64_to_usize(v___y_276_);
v___x_278_ = ((size_t)5ULL);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_sub(v_depth_266_, v___x_280_);
v___x_282_ = lean_usize_mul(v___x_278_, v___x_281_);
v_h_283_ = lean_usize_shift_right(v_h_277_, v___x_282_);
v___x_284_ = lean_nat_add(v_i_269_, v___x_279_);
lean_dec(v_i_269_);
lean_inc(v_v_274_);
lean_inc(v_k_273_);
v___x_285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_270_, v_h_283_, v_depth_266_, v_k_273_, v_v_274_);
v_i_269_ = v___x_284_;
v_entries_270_ = v___x_285_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_266_ = stack[0].m_num;
lean_object* v_keys_267_ = stack[1].m_obj;
lean_object* v_vals_268_ = stack[2].m_obj;
lean_object* v_i_269_ = stack[3].m_obj;
lean_object* v_entries_270_ = stack[4].m_obj;
lean_object* v_res_289_;
v_res_289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_266_, v_keys_267_, v_vals_268_, v_i_269_, v_entries_270_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_290_, lean_object* v_keys_291_, lean_object* v_vals_292_, lean_object* v_i_293_, lean_object* v_entries_294_){
_start:
{
size_t v_depth_boxed_295_; lean_object* v_res_296_; 
v_depth_boxed_295_ = lean_unbox_usize(v_depth_290_);
lean_dec(v_depth_290_);
v_res_296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_295_, v_keys_291_, v_vals_292_, v_i_293_, v_entries_294_);
lean_dec_ref(v_vals_292_);
lean_dec_ref(v_keys_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
size_t v_x_1106__boxed_302_; size_t v_x_1107__boxed_303_; lean_object* v_res_304_; 
v_x_1106__boxed_302_ = lean_unbox_usize(v_x_298_);
lean_dec(v_x_298_);
v_x_1107__boxed_303_ = lean_unbox_usize(v_x_299_);
lean_dec(v_x_299_);
v_res_304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_297_, v_x_1106__boxed_302_, v_x_1107__boxed_303_, v_x_300_, v_x_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint64_t v___y_309_; 
if (lean_obj_tag(v_x_306_) == 0)
{
uint64_t v___x_313_; 
v___x_313_ = 1723ULL;
v___y_309_ = v___x_313_;
goto v___jp_308_;
}
else
{
uint64_t v_hash_314_; 
v_hash_314_ = lean_ctor_get_uint64(v_x_306_, sizeof(void*)*2);
v___y_309_ = v_hash_314_;
goto v___jp_308_;
}
v___jp_308_:
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_uint64_to_usize(v___y_309_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_305_, v___x_310_, v___x_311_, v_x_306_, v_x_307_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
return v_x_315_;
}
else
{
lean_object* v_key_317_; lean_object* v_value_318_; lean_object* v_tail_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_345_; 
v_key_317_ = lean_ctor_get(v_x_316_, 0);
v_value_318_ = lean_ctor_get(v_x_316_, 1);
v_tail_319_ = lean_ctor_get(v_x_316_, 2);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_345_ == 0)
{
v___x_321_ = v_x_316_;
v_isShared_322_ = v_isSharedCheck_345_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_tail_319_);
lean_inc(v_value_318_);
lean_inc(v_key_317_);
lean_dec(v_x_316_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_345_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; uint64_t v___y_325_; 
v___x_323_ = lean_array_get_size(v_x_315_);
if (lean_obj_tag(v_key_317_) == 0)
{
uint64_t v___x_343_; 
v___x_343_ = 1723ULL;
v___y_325_ = v___x_343_;
goto v___jp_324_;
}
else
{
uint64_t v_hash_344_; 
v_hash_344_ = lean_ctor_get_uint64(v_key_317_, sizeof(void*)*2);
v___y_325_ = v_hash_344_;
goto v___jp_324_;
}
v___jp_324_:
{
uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v_fold_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_326_ = 32ULL;
v___x_327_ = lean_uint64_shift_right(v___y_325_, v___x_326_);
v_fold_328_ = lean_uint64_xor(v___y_325_, v___x_327_);
v___x_329_ = 16ULL;
v___x_330_ = lean_uint64_shift_right(v_fold_328_, v___x_329_);
v___x_331_ = lean_uint64_xor(v_fold_328_, v___x_330_);
v___x_332_ = lean_uint64_to_usize(v___x_331_);
v___x_333_ = lean_usize_of_nat(v___x_323_);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_sub(v___x_333_, v___x_334_);
v___x_336_ = lean_usize_land(v___x_332_, v___x_335_);
v___x_337_ = lean_array_uget_borrowed(v_x_315_, v___x_336_);
lean_inc(v___x_337_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 2, v___x_337_);
v___x_339_ = v___x_321_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_key_317_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_value_318_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v___x_337_);
v___x_339_ = v_reuseFailAlloc_342_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_uset(v_x_315_, v___x_336_, v___x_339_);
v_x_315_ = v___x_340_;
v_x_316_ = v_tail_319_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_346_, lean_object* v_source_347_, lean_object* v_target_348_){
_start:
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_array_get_size(v_source_347_);
v___x_350_ = lean_nat_dec_lt(v_i_346_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec_ref(v_source_347_);
lean_dec(v_i_346_);
return v_target_348_;
}
else
{
lean_object* v_es_351_; lean_object* v___x_352_; lean_object* v_source_353_; lean_object* v_target_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_es_351_ = lean_array_fget(v_source_347_, v_i_346_);
v___x_352_ = lean_box(0);
v_source_353_ = lean_array_fset(v_source_347_, v_i_346_, v___x_352_);
v_target_354_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_348_, v_es_351_);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_i_346_, v___x_355_);
lean_dec(v_i_346_);
v_i_346_ = v___x_356_;
v_source_347_ = v_source_353_;
v_target_348_ = v_target_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_nbuckets_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_359_ = lean_array_get_size(v_data_358_);
v___x_360_ = lean_unsigned_to_nat(2u);
v_nbuckets_361_ = lean_nat_mul(v___x_359_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_box(0);
v___x_364_ = lean_mk_array(v_nbuckets_361_, v___x_363_);
v___x_365_ = lean_array_propagate_mark(v_data_358_, v___x_364_);
v___x_366_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_362_, v_data_358_, v___x_365_);
return v___x_366_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
else
{
lean_object* v_key_370_; lean_object* v_tail_371_; uint8_t v___x_372_; 
v_key_370_ = lean_ctor_get(v_x_368_, 0);
v_tail_371_ = lean_ctor_get(v_x_368_, 2);
v___x_372_ = lean_name_eq(v_key_370_, v_a_367_);
if (v___x_372_ == 0)
{
v_x_368_ = v_tail_371_;
goto _start;
}
else
{
return v___x_372_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_367_ = stack[0].m_obj;
lean_object* v_x_368_ = stack[1].m_obj;
uint8_t v_res_374_;
v_res_374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_367_, v_x_368_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_375_, lean_object* v_x_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_375_, v_x_376_);
lean_dec(v_x_376_);
lean_dec(v_a_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_379_, lean_object* v_b_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_dec(v_b_380_);
lean_dec(v_a_379_);
return v_x_381_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_396_; 
v_key_382_ = lean_ctor_get(v_x_381_, 0);
v_value_383_ = lean_ctor_get(v_x_381_, 1);
v_tail_384_ = lean_ctor_get(v_x_381_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_396_ == 0)
{
v___x_386_ = v_x_381_;
v_isShared_387_ = v_isSharedCheck_396_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_tail_384_);
lean_inc(v_value_383_);
lean_inc(v_key_382_);
lean_dec(v_x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_396_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint8_t v___x_388_; 
v___x_388_ = lean_name_eq(v_key_382_, v_a_379_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_379_, v_b_380_, v_tail_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_key_382_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_value_383_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
else
{
lean_object* v___x_394_; 
lean_dec(v_value_383_);
lean_dec(v_key_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_b_380_);
lean_ctor_set(v___x_386_, 0, v_a_379_);
v___x_394_ = v___x_386_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_b_380_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_tail_384_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_397_, lean_object* v_a_398_, lean_object* v_b_399_){
_start:
{
lean_object* v_size_400_; lean_object* v_buckets_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_447_; 
v_size_400_ = lean_ctor_get(v_m_397_, 0);
v_buckets_401_ = lean_ctor_get(v_m_397_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_m_397_);
if (v_isSharedCheck_447_ == 0)
{
v___x_403_ = v_m_397_;
v_isShared_404_ = v_isSharedCheck_447_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_buckets_401_);
lean_inc(v_size_400_);
lean_dec(v_m_397_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_447_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; uint64_t v___y_407_; 
v___x_405_ = lean_array_get_size(v_buckets_401_);
if (lean_obj_tag(v_a_398_) == 0)
{
uint64_t v___x_445_; 
v___x_445_ = 1723ULL;
v___y_407_ = v___x_445_;
goto v___jp_406_;
}
else
{
uint64_t v_hash_446_; 
v_hash_446_ = lean_ctor_get_uint64(v_a_398_, sizeof(void*)*2);
v___y_407_ = v_hash_446_;
goto v___jp_406_;
}
v___jp_406_:
{
uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v_fold_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v_bkt_419_; uint8_t v___x_420_; 
v___x_408_ = 32ULL;
v___x_409_ = lean_uint64_shift_right(v___y_407_, v___x_408_);
v_fold_410_ = lean_uint64_xor(v___y_407_, v___x_409_);
v___x_411_ = 16ULL;
v___x_412_ = lean_uint64_shift_right(v_fold_410_, v___x_411_);
v___x_413_ = lean_uint64_xor(v_fold_410_, v___x_412_);
v___x_414_ = lean_uint64_to_usize(v___x_413_);
v___x_415_ = lean_usize_of_nat(v___x_405_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_sub(v___x_415_, v___x_416_);
v___x_418_ = lean_usize_land(v___x_414_, v___x_417_);
v_bkt_419_ = lean_array_uget_borrowed(v_buckets_401_, v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_398_, v_bkt_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v_size_x27_422_; lean_object* v___x_423_; lean_object* v_buckets_x27_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v_size_x27_422_ = lean_nat_add(v_size_400_, v___x_421_);
lean_dec(v_size_400_);
lean_inc(v_bkt_419_);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v_a_398_);
lean_ctor_set(v___x_423_, 1, v_b_399_);
lean_ctor_set(v___x_423_, 2, v_bkt_419_);
v_buckets_x27_424_ = lean_array_uset(v_buckets_401_, v___x_418_, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(4u);
v___x_426_ = lean_nat_mul(v_size_x27_422_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(3u);
v___x_428_ = lean_nat_div(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_array_get_size(v_buckets_x27_424_);
v___x_430_ = lean_nat_dec_le(v___x_428_, v___x_429_);
lean_dec(v___x_428_);
if (v___x_430_ == 0)
{
lean_object* v_val_431_; lean_object* v___x_433_; 
v_val_431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_424_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_val_431_);
lean_ctor_set(v___x_403_, 0, v_size_x27_422_);
v___x_433_ = v___x_403_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_val_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_object* v___x_436_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_buckets_x27_424_);
lean_ctor_set(v___x_403_, 0, v_size_x27_422_);
v___x_436_ = v___x_403_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_buckets_x27_424_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v___x_438_; lean_object* v_buckets_x27_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
lean_inc(v_bkt_419_);
v___x_438_ = lean_box(0);
v_buckets_x27_439_ = lean_array_uset(v_buckets_401_, v___x_418_, v___x_438_);
v___x_440_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_398_, v_b_399_, v_bkt_419_);
v___x_441_ = lean_array_uset(v_buckets_x27_439_, v___x_418_, v___x_440_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v___x_441_);
v___x_443_ = v___x_403_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_size_400_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
uint8_t v_stage_u2081_451_; 
v_stage_u2081_451_ = lean_ctor_get_uint8(v_x_448_, sizeof(void*)*2);
if (v_stage_u2081_451_ == 0)
{
lean_object* v_map_u2081_452_; lean_object* v_map_u2082_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_map_u2081_452_ = lean_ctor_get(v_x_448_, 0);
v_map_u2082_453_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v_x_448_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_map_u2082_453_);
lean_inc(v_map_u2081_452_);
lean_dec(v_x_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_453_, v_x_449_, v_x_450_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_map_u2081_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_460_, sizeof(void*)*2, v_stage_u2081_451_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v_map_u2081_462_; lean_object* v_map_u2082_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
v_map_u2081_462_ = lean_ctor_get(v_x_448_, 0);
v_map_u2082_463_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_471_ == 0)
{
v___x_465_ = v_x_448_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_map_u2082_463_);
lean_inc(v_map_u2081_462_);
lean_dec(v_x_448_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_462_, v_x_449_, v_x_450_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_map_u2082_463_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, sizeof(void*)*2, v_stage_u2081_451_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_472_, lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v_key_475_; lean_object* v_value_476_; lean_object* v_tail_477_; uint8_t v___x_478_; 
v_key_475_ = lean_ctor_get(v_x_473_, 0);
v_value_476_ = lean_ctor_get(v_x_473_, 1);
v_tail_477_ = lean_ctor_get(v_x_473_, 2);
v___x_478_ = lean_name_eq(v_key_475_, v_a_472_);
if (v___x_478_ == 0)
{
v_x_473_ = v_tail_477_;
goto _start;
}
else
{
lean_object* v___x_480_; 
lean_inc(v_value_476_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v_value_476_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_481_, v_x_482_);
lean_dec(v_x_482_);
lean_dec(v_a_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_buckets_486_; lean_object* v___x_487_; uint64_t v___y_489_; 
v_buckets_486_ = lean_ctor_get(v_m_484_, 1);
v___x_487_ = lean_array_get_size(v_buckets_486_);
if (lean_obj_tag(v_a_485_) == 0)
{
uint64_t v___x_503_; 
v___x_503_ = 1723ULL;
v___y_489_ = v___x_503_;
goto v___jp_488_;
}
else
{
uint64_t v_hash_504_; 
v_hash_504_ = lean_ctor_get_uint64(v_a_485_, sizeof(void*)*2);
v___y_489_ = v_hash_504_;
goto v___jp_488_;
}
v___jp_488_:
{
uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v_fold_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; size_t v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_490_ = 32ULL;
v___x_491_ = lean_uint64_shift_right(v___y_489_, v___x_490_);
v_fold_492_ = lean_uint64_xor(v___y_489_, v___x_491_);
v___x_493_ = 16ULL;
v___x_494_ = lean_uint64_shift_right(v_fold_492_, v___x_493_);
v___x_495_ = lean_uint64_xor(v_fold_492_, v___x_494_);
v___x_496_ = lean_uint64_to_usize(v___x_495_);
v___x_497_ = lean_usize_of_nat(v___x_487_);
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_sub(v___x_497_, v___x_498_);
v___x_500_ = lean_usize_land(v___x_496_, v___x_499_);
v___x_501_ = lean_array_uget_borrowed(v_buckets_486_, v___x_500_);
v___x_502_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_485_, v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_m_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_508_, lean_object* v_vals_509_, lean_object* v_i_510_, lean_object* v_k_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_array_get_size(v_keys_508_);
v___x_513_ = lean_nat_dec_lt(v_i_510_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_i_510_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v_k_x27_515_; uint8_t v___x_516_; 
v_k_x27_515_ = lean_array_fget_borrowed(v_keys_508_, v_i_510_);
v___x_516_ = lean_name_eq(v_k_511_, v_k_x27_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_i_510_, v___x_517_);
lean_dec(v_i_510_);
v_i_510_ = v___x_518_;
goto _start;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_array_fget_borrowed(v_vals_509_, v_i_510_);
lean_dec(v_i_510_);
lean_inc(v___x_520_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_522_, lean_object* v_vals_523_, lean_object* v_i_524_, lean_object* v_k_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_522_, v_vals_523_, v_i_524_, v_k_525_);
lean_dec(v_k_525_);
lean_dec_ref(v_vals_523_);
lean_dec_ref(v_keys_522_);
return v_res_526_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_527_, size_t v_x_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v_es_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v_j_534_; lean_object* v___x_535_; 
v_es_530_ = lean_ctor_get(v_x_527_, 0);
v___x_531_ = lean_box(2);
v___x_532_ = ((size_t)31ULL);
v___x_533_ = lean_usize_land(v_x_528_, v___x_532_);
v_j_534_ = lean_usize_to_nat(v___x_533_);
v___x_535_ = lean_array_get_borrowed(v___x_531_, v_es_530_, v_j_534_);
lean_dec(v_j_534_);
switch(lean_obj_tag(v___x_535_))
{
case 0:
{
lean_object* v_key_536_; lean_object* v_val_537_; uint8_t v___x_538_; 
v_key_536_ = lean_ctor_get(v___x_535_, 0);
v_val_537_ = lean_ctor_get(v___x_535_, 1);
v___x_538_ = lean_name_eq(v_x_529_, v_key_536_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(0);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
lean_inc(v_val_537_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_val_537_);
return v___x_540_;
}
}
case 1:
{
lean_object* v_node_541_; size_t v___x_542_; size_t v___x_543_; 
v_node_541_ = lean_ctor_get(v___x_535_, 0);
v___x_542_ = ((size_t)5ULL);
v___x_543_ = lean_usize_shift_right(v_x_528_, v___x_542_);
v_x_527_ = v_node_541_;
v_x_528_ = v___x_543_;
goto _start;
}
default: 
{
lean_object* v___x_545_; 
v___x_545_ = lean_box(0);
return v___x_545_;
}
}
}
else
{
lean_object* v_ks_546_; lean_object* v_vs_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_ks_546_ = lean_ctor_get(v_x_527_, 0);
v_vs_547_ = lean_ctor_get(v_x_527_, 1);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_546_, v_vs_547_, v___x_548_, v_x_529_);
return v___x_549_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_527_ = stack[0].m_obj;
size_t v_x_528_ = stack[1].m_num;
lean_object* v_x_529_ = stack[2].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_527_, v_x_528_, v_x_529_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
size_t v_x_1871__boxed_554_; lean_object* v_res_555_; 
v_x_1871__boxed_554_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_res_555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_551_, v_x_1871__boxed_554_, v_x_553_);
lean_dec(v_x_553_);
lean_dec_ref(v_x_551_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
uint64_t v___y_559_; 
if (lean_obj_tag(v_x_557_) == 0)
{
uint64_t v___x_562_; 
v___x_562_ = 1723ULL;
v___y_559_ = v___x_562_;
goto v___jp_558_;
}
else
{
uint64_t v_hash_563_; 
v_hash_563_ = lean_ctor_get_uint64(v_x_557_, sizeof(void*)*2);
v___y_559_ = v_hash_563_;
goto v___jp_558_;
}
v___jp_558_:
{
size_t v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_uint64_to_usize(v___y_559_);
v___x_561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_556_, v___x_560_, v_x_557_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_564_, v_x_565_);
lean_dec(v_x_565_);
lean_dec_ref(v_x_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
uint8_t v_stage_u2081_569_; 
v_stage_u2081_569_ = lean_ctor_get_uint8(v_x_567_, sizeof(void*)*2);
if (v_stage_u2081_569_ == 0)
{
lean_object* v_map_u2081_570_; lean_object* v_map_u2082_571_; lean_object* v___x_572_; 
v_map_u2081_570_ = lean_ctor_get(v_x_567_, 0);
v_map_u2082_571_ = lean_ctor_get(v_x_567_, 1);
v___x_572_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_571_, v_x_568_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_570_, v_x_568_);
return v___x_573_;
}
else
{
return v___x_572_;
}
}
else
{
lean_object* v_map_u2081_574_; lean_object* v___x_575_; 
v_map_u2081_574_ = lean_ctor_get(v_x_567_, 0);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_574_, v_x_568_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec_ref(v_x_576_);
return v_res_578_;
}
}
uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
uint8_t v___x_581_; 
v___x_581_ = 0;
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; uint8_t v___x_584_; 
v_head_582_ = lean_ctor_get(v_x_580_, 0);
v_tail_583_ = lean_ctor_get(v_x_580_, 1);
v___x_584_ = lean_name_eq(v_a_579_, v_head_582_);
if (v___x_584_ == 0)
{
v_x_580_ = v_tail_583_;
goto _start;
}
else
{
return v___x_584_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_addAliasEntry_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_579_ = stack[0].m_obj;
lean_object* v_x_580_ = stack[1].m_obj;
uint8_t v_res_586_;
v_res_586_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_579_, v_x_580_);
stack->m_num = v_res_586_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_587_, lean_object* v_x_588_){
_start:
{
uint8_t v_res_589_; lean_object* v_r_590_; 
v_res_589_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_587_, v_x_588_);
lean_dec(v_x_588_);
lean_dec(v_a_587_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_591_, lean_object* v_e_592_){
_start:
{
lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_610_; 
v_fst_593_ = lean_ctor_get(v_e_592_, 0);
v_snd_594_ = lean_ctor_get(v_e_592_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_e_592_);
if (v_isSharedCheck_610_ == 0)
{
v___x_596_ = v_e_592_;
v_isShared_597_ = v_isSharedCheck_610_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snd_594_);
lean_inc(v_fst_593_);
lean_dec(v_e_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_610_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_591_, v_fst_593_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 1);
lean_ctor_set(v___x_596_, 1, v___x_599_);
lean_ctor_set(v___x_596_, 0, v_snd_594_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_snd_594_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_599_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_591_, v_fst_593_, v___x_601_);
return v___x_602_;
}
}
else
{
lean_object* v_val_604_; uint8_t v___x_605_; 
v_val_604_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v___x_598_, 1);
v___x_605_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_594_, v_val_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_607_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 1);
lean_ctor_set(v___x_596_, 1, v_val_604_);
lean_ctor_set(v___x_596_, 0, v_snd_594_);
v___x_607_ = v___x_596_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_snd_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_val_604_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_591_, v_fst_593_, v___x_607_);
return v___x_608_;
}
}
else
{
lean_dec(v_val_604_);
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
return v_s_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_615_, v_x_616_, v_x_617_);
lean_dec(v_x_617_);
lean_dec_ref(v_x_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_620_, v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_628_, v_x_629_, v_x_630_);
lean_dec(v_x_630_);
lean_dec_ref(v_x_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_632_, lean_object* v_m_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_633_, v_a_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_636_, lean_object* v_m_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_636_, v_m_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_m_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_641_, v_x_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_645_, lean_object* v_m_646_, lean_object* v_a_647_, lean_object* v_b_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_646_, v_a_647_, v_b_648_);
return v___x_649_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, size_t v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_651_, v_x_652_, v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_651_ = stack[1].m_obj;
size_t v_x_652_ = stack[2].m_num;
lean_object* v_x_653_ = stack[3].m_obj;
lean_object* v_res_655_;
v_res_655_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_box(0), v_x_651_, v_x_652_, v_x_653_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
size_t v_x_2124__boxed_660_; lean_object* v_res_661_; 
v_x_2124__boxed_660_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_res_661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_656_, v_x_657_, v_x_2124__boxed_660_, v_x_659_);
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
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, size_t v_x_672_, size_t v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_671_, v_x_672_, v_x_673_, v_x_674_, v_x_675_);
return v___x_676_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_671_ = stack[1].m_obj;
size_t v_x_672_ = stack[2].m_num;
size_t v_x_673_ = stack[3].m_num;
lean_object* v_x_674_ = stack[4].m_obj;
lean_object* v_x_675_ = stack[5].m_obj;
lean_object* v_res_677_;
v_res_677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_box(0), v_x_671_, v_x_672_, v_x_673_, v_x_674_, v_x_675_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
size_t v_x_2150__boxed_684_; size_t v_x_2151__boxed_685_; lean_object* v_res_686_; 
v_x_2150__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_x_2151__boxed_685_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_res_686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_678_, v_x_679_, v_x_2150__boxed_684_, v_x_2151__boxed_685_, v_x_682_, v_x_683_);
return v_res_686_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_687_, lean_object* v_a_688_, lean_object* v_x_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_688_ = stack[1].m_obj;
lean_object* v_x_689_ = stack[2].m_obj;
uint8_t v_res_691_;
v_res_691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_box(0), v_a_688_, v_x_689_);
stack->m_num = v_res_691_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_692_, lean_object* v_a_693_, lean_object* v_x_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_692_, v_a_693_, v_x_694_);
lean_dec(v_x_694_);
lean_dec(v_a_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_697_, lean_object* v_data_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_700_, lean_object* v_a_701_, lean_object* v_b_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_701_, v_b_702_, v_x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_705_, lean_object* v_keys_706_, lean_object* v_vals_707_, lean_object* v_heq_708_, lean_object* v_i_709_, lean_object* v_k_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_706_, v_vals_707_, v_i_709_, v_k_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_712_, lean_object* v_keys_713_, lean_object* v_vals_714_, lean_object* v_heq_715_, lean_object* v_i_716_, lean_object* v_k_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_712_, v_keys_713_, v_vals_714_, v_heq_715_, v_i_716_, v_k_717_);
lean_dec(v_k_717_);
lean_dec_ref(v_vals_714_);
lean_dec_ref(v_keys_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_719_, lean_object* v_n_720_, lean_object* v_k_721_, lean_object* v_v_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_720_, v_k_721_, v_v_722_);
return v___x_723_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_724_, size_t v_depth_725_, lean_object* v_keys_726_, lean_object* v_vals_727_, lean_object* v_heq_728_, lean_object* v_i_729_, lean_object* v_entries_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_725_, v_keys_726_, v_vals_727_, v_i_729_, v_entries_730_);
return v___x_731_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_depth_725_ = stack[1].m_num;
lean_object* v_keys_726_ = stack[2].m_obj;
lean_object* v_vals_727_ = stack[3].m_obj;
lean_object* v_i_729_ = stack[5].m_obj;
lean_object* v_entries_730_ = stack[6].m_obj;
lean_object* v_res_732_;
v_res_732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_box(0), v_depth_725_, v_keys_726_, v_vals_727_, lean_box(0), v_i_729_, v_entries_730_);
stack->m_obj
 = v_res_732_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_733_, lean_object* v_depth_734_, lean_object* v_keys_735_, lean_object* v_vals_736_, lean_object* v_heq_737_, lean_object* v_i_738_, lean_object* v_entries_739_){
_start:
{
size_t v_depth_boxed_740_; lean_object* v_res_741_; 
v_depth_boxed_740_ = lean_unbox_usize(v_depth_734_);
lean_dec(v_depth_734_);
v_res_741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_733_, v_depth_boxed_740_, v_keys_735_, v_vals_736_, v_heq_737_, v_i_738_, v_entries_739_);
lean_dec_ref(v_vals_736_);
lean_dec_ref(v_keys_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_742_, lean_object* v_i_743_, lean_object* v_source_744_, lean_object* v_target_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_743_, v_source_744_, v_target_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_748_, v_x_749_, v_x_750_, v_x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_757_){
_start:
{
uint8_t v_stage_u2081_758_; 
v_stage_u2081_758_ = lean_ctor_get_uint8(v_m_757_, sizeof(void*)*2);
if (v_stage_u2081_758_ == 0)
{
return v_m_757_;
}
else
{
lean_object* v_map_u2081_759_; lean_object* v_map_u2082_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_map_u2081_759_ = lean_ctor_get(v_m_757_, 0);
v_map_u2082_760_ = lean_ctor_get(v_m_757_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_m_757_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v_m_757_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_map_u2082_760_);
lean_inc(v_map_u2081_759_);
lean_dec(v_m_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; lean_object* v___x_766_; 
v___x_764_ = 0;
if (v_isShared_763_ == 0)
{
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_map_u2081_759_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_map_u2082_760_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*2, v___x_764_);
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_769_, lean_object* v_m_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_array_mk(v_es_772_);
return v___x_773_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_774_, size_t v_i_775_, size_t v_stop_776_, lean_object* v_b_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_eq(v_i_775_, v_stop_776_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; size_t v___x_781_; size_t v___x_782_; 
v___x_779_ = lean_array_uget_borrowed(v_as_774_, v_i_775_);
lean_inc(v___x_779_);
v___x_780_ = l_Lean_addAliasEntry(v_b_777_, v___x_779_);
v___x_781_ = ((size_t)1ULL);
v___x_782_ = lean_usize_add(v_i_775_, v___x_781_);
v_i_775_ = v___x_782_;
v_b_777_ = v___x_780_;
goto _start;
}
else
{
return v_b_777_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_774_ = stack[0].m_obj;
size_t v_i_775_ = stack[1].m_num;
size_t v_stop_776_ = stack[2].m_num;
lean_object* v_b_777_ = stack[3].m_obj;
lean_object* v_res_784_;
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_774_, v_i_775_, v_stop_776_, v_b_777_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_785_, lean_object* v_i_786_, lean_object* v_stop_787_, lean_object* v_b_788_){
_start:
{
size_t v_i_boxed_789_; size_t v_stop_boxed_790_; lean_object* v_res_791_; 
v_i_boxed_789_ = lean_unbox_usize(v_i_786_);
lean_dec(v_i_786_);
v_stop_boxed_790_ = lean_unbox_usize(v_stop_787_);
lean_dec(v_stop_787_);
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_785_, v_i_boxed_789_, v_stop_boxed_790_, v_b_788_);
lean_dec_ref(v_as_785_);
return v_res_791_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_792_, size_t v_i_793_, size_t v_stop_794_, lean_object* v_b_795_){
_start:
{
lean_object* v___y_797_; uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_eq(v_i_793_, v_stop_794_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_802_ = lean_array_uget_borrowed(v_as_792_, v_i_793_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_array_get_size(v___x_802_);
v___x_805_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
v___y_797_ = v_b_795_;
goto v___jp_796_;
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_804_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_802_, v___x_806_, v___x_807_, v_b_795_);
v___y_797_ = v___x_808_;
goto v___jp_796_;
}
}
else
{
return v_b_795_;
}
v___jp_796_:
{
size_t v___x_798_; size_t v___x_799_; 
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_793_, v___x_798_);
v_i_793_ = v___x_799_;
v_b_795_ = v___y_797_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_792_ = stack[0].m_obj;
size_t v_i_793_ = stack[1].m_num;
size_t v_stop_794_ = stack[2].m_num;
lean_object* v_b_795_ = stack[3].m_obj;
lean_object* v_res_809_;
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_792_, v_i_793_, v_stop_794_, v_b_795_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_810_, lean_object* v_i_811_, lean_object* v_stop_812_, lean_object* v_b_813_){
_start:
{
size_t v_i_boxed_814_; size_t v_stop_boxed_815_; lean_object* v_res_816_; 
v_i_boxed_814_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_stop_boxed_815_ = lean_unbox_usize(v_stop_812_);
lean_dec(v_stop_812_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_810_, v_i_boxed_814_, v_stop_boxed_815_, v_b_813_);
lean_dec_ref(v_as_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_817_, lean_object* v_as_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_array_get_size(v_as_818_);
v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
if (v___x_821_ == 0)
{
return v_initState_817_;
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_820_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_818_, v___x_822_, v___x_823_, v_initState_817_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_825_, lean_object* v_as_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_825_, v_as_826_);
lean_dec_ref(v_as_826_);
return v_res_827_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_unsigned_to_nat(16u);
v___x_830_ = lean_mk_array(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_834_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v___x_837_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_838_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_839_ = 1;
v___x_840_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*2, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_843_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_842_, v_es_841_);
v___x_844_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_845_);
lean_dec_ref(v_es_845_);
return v_res_846_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_864_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_865_;
v_res_865_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
stack->m_obj
 = v_res_865_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias___lam__0(lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v_s_870_){
_start:
{
lean_object* v_addEntryFn_871_; lean_object* v_importedEntries_872_; lean_object* v_state_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_addEntryFn_871_ = lean_ctor_get(v___x_868_, 3);
lean_inc(v_addEntryFn_871_);
lean_dec_ref(v___x_868_);
v_importedEntries_872_ = lean_ctor_get(v_s_870_, 0);
v_state_873_ = lean_ctor_get(v_s_870_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_s_870_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v_s_870_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_state_873_);
lean_inc(v_importedEntries_872_);
lean_dec(v_s_870_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_state_877_; lean_object* v___x_879_; 
v_state_877_ = lean_apply_2(v_addEntryFn_871_, v_state_873_, v___x_869_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_state_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_importedEntries_872_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_state_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_882_, lean_object* v_a_883_, lean_object* v_e_884_){
_start:
{
lean_object* v___x_885_; lean_object* v_toEnvExtension_886_; lean_object* v_asyncMode_887_; uint8_t v_logWrites_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_885_ = l_Lean_aliasExtension;
v_toEnvExtension_886_ = lean_ctor_get(v___x_885_, 0);
v_asyncMode_887_ = lean_ctor_get(v_toEnvExtension_886_, 2);
v_logWrites_888_ = lean_ctor_get_uint8(v_toEnvExtension_886_, sizeof(void*)*6);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_a_883_);
lean_ctor_set(v___x_889_, 1, v_e_884_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_addAlias___lam__0), 3, 2);
lean_closure_set(v___f_890_, 0, v___x_885_);
lean_closure_set(v___f_890_, 1, v___x_889_);
v___x_891_ = lean_box(0);
v___x_892_ = 1;
if (v_logWrites_888_ == 0)
{
lean_object* v___x_893_; 
lean_inc_ref(v_toEnvExtension_886_);
v___x_893_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_886_, v_env_882_, v___f_890_, v_asyncMode_887_, v___x_891_, v___x_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc_ref_n(v_toEnvExtension_886_, 2);
v___x_894_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_886_, v_env_882_);
lean_dec_ref(v_env_882_);
v___x_895_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_886_, v___x_894_, v___f_890_, v_asyncMode_887_, v___x_891_, v___x_892_);
return v___x_895_;
}
}
}
static lean_object* _init_l_Lean_getAliasState___closed__0(void){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_SMap_instInhabited___redArg();
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_897_){
_start:
{
lean_object* v___x_898_; lean_object* v_toEnvExtension_899_; lean_object* v_asyncMode_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_898_ = l_Lean_aliasExtension;
v_toEnvExtension_899_ = lean_ctor_get(v___x_898_, 0);
v_asyncMode_900_ = lean_ctor_get(v_toEnvExtension_899_, 2);
v___x_901_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_902_ = lean_box(0);
v___x_903_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_901_, v___x_898_, v_env_897_, v_asyncMode_900_, v___x_902_);
return v___x_903_;
}
}
lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_904_, uint8_t v_skipProtected_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
if (lean_obj_tag(v_a_906_) == 0)
{
lean_object* v___x_908_; 
lean_dec_ref(v_env_904_);
v___x_908_ = l_List_reverse___redArg(v_a_907_);
return v___x_908_;
}
else
{
lean_object* v_head_909_; lean_object* v_tail_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_921_; 
v_head_909_ = lean_ctor_get(v_a_906_, 0);
v_tail_910_ = lean_ctor_get(v_a_906_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_906_);
if (v_isSharedCheck_921_ == 0)
{
v___x_912_ = v_a_906_;
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_tail_910_);
lean_inc(v_head_909_);
lean_dec(v_a_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___x_914_; 
lean_inc(v_head_909_);
lean_inc_ref(v_env_904_);
v___x_914_ = l_Lean_isProtected(v_env_904_, v_head_909_);
if (v___x_914_ == 0)
{
if (v_skipProtected_905_ == 0)
{
lean_del_object(v___x_912_);
lean_dec(v_head_909_);
v_a_906_ = v_tail_910_;
goto _start;
}
else
{
lean_object* v___x_917_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_a_907_);
v___x_917_ = v___x_912_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_head_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_a_907_);
v___x_917_ = v_reuseFailAlloc_919_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
v_a_906_ = v_tail_910_;
v_a_907_ = v___x_917_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_912_);
lean_dec(v_head_909_);
v_a_906_ = v_tail_910_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_filterTR_loop___at___00Lean_getAliases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_904_ = stack[0].m_obj;
uint8_t v_skipProtected_905_ = stack[1].m_num;
lean_object* v_a_906_ = stack[2].m_obj;
lean_object* v_a_907_ = stack[3].m_obj;
lean_object* v_res_922_;
v_res_922_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_904_, v_skipProtected_905_, v_a_906_, v_a_907_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_923_, lean_object* v_skipProtected_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
uint8_t v_skipProtected_boxed_927_; lean_object* v_res_928_; 
v_skipProtected_boxed_927_ = lean_unbox(v_skipProtected_924_);
v_res_928_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_923_, v_skipProtected_boxed_927_, v_a_925_, v_a_926_);
return v_res_928_;
}
}
lean_object* l_Lean_getAliases(lean_object* v_env_929_, lean_object* v_a_930_, uint8_t v_skipProtected_931_){
_start:
{
lean_object* v___x_932_; lean_object* v_toEnvExtension_933_; lean_object* v_asyncMode_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_932_ = l_Lean_aliasExtension;
v_toEnvExtension_933_ = lean_ctor_get(v___x_932_, 0);
v_asyncMode_934_ = lean_ctor_get(v_toEnvExtension_933_, 2);
v___x_935_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_936_ = lean_box(0);
lean_inc_ref(v_env_929_);
v___x_937_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_935_, v___x_932_, v_env_929_, v_asyncMode_934_, v___x_936_);
v___x_938_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_937_, v_a_930_);
lean_dec(v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v_env_929_);
v___x_939_ = lean_box(0);
return v___x_939_;
}
else
{
if (v_skipProtected_931_ == 0)
{
lean_object* v_val_940_; 
lean_dec_ref(v_env_929_);
v_val_940_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___x_938_, 1);
return v_val_940_;
}
else
{
lean_object* v_val_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_val_941_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v___x_938_, 1);
v___x_942_ = lean_box(0);
v___x_943_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_929_, v_skipProtected_931_, v_val_941_, v___x_942_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT void l_Lean_getAliases_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_929_ = stack[0].m_obj;
lean_object* v_a_930_ = stack[1].m_obj;
uint8_t v_skipProtected_931_ = stack[2].m_num;
lean_object* v_res_944_;
v_res_944_ = l_Lean_getAliases(v_env_929_, v_a_930_, v_skipProtected_931_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_945_, lean_object* v_a_946_, lean_object* v_skipProtected_947_){
_start:
{
uint8_t v_skipProtected_boxed_948_; lean_object* v_res_949_; 
v_skipProtected_boxed_948_ = lean_unbox(v_skipProtected_947_);
v_res_949_ = l_Lean_getAliases(v_env_945_, v_a_946_, v_skipProtected_boxed_948_);
lean_dec(v_a_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_950_, lean_object* v_as_951_, lean_object* v_a_952_, lean_object* v_es_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_950_, v_es_953_);
if (v___x_954_ == 0)
{
lean_dec(v_a_952_);
return v_as_951_;
}
else
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v_a_952_);
lean_ctor_set(v___x_955_, 1, v_as_951_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_956_, lean_object* v_as_957_, lean_object* v_a_958_, lean_object* v_es_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_getRevAliases___lam__0(v_e_956_, v_as_957_, v_a_958_, v_es_959_);
lean_dec(v_es_959_);
lean_dec(v_e_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_961_, lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_i_964_, lean_object* v_acc_965_){
_start:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_get_size(v_keys_962_);
v___x_967_ = lean_nat_dec_lt(v_i_964_, v___x_966_);
if (v___x_967_ == 0)
{
lean_dec(v_i_964_);
lean_dec(v_f_961_);
return v_acc_965_;
}
else
{
lean_object* v_k_968_; lean_object* v_v_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_k_968_ = lean_array_fget_borrowed(v_keys_962_, v_i_964_);
v_v_969_ = lean_array_fget_borrowed(v_vals_963_, v_i_964_);
lean_inc(v_f_961_);
lean_inc(v_v_969_);
lean_inc(v_k_968_);
v___x_970_ = lean_apply_3(v_f_961_, v_acc_965_, v_k_968_, v_v_969_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_i_964_, v___x_971_);
lean_dec(v_i_964_);
v_i_964_ = v___x_972_;
v_acc_965_ = v___x_970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_974_, lean_object* v_keys_975_, lean_object* v_vals_976_, lean_object* v_i_977_, lean_object* v_acc_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_974_, v_keys_975_, v_vals_976_, v_i_977_, v_acc_978_);
lean_dec_ref(v_vals_976_);
lean_dec_ref(v_keys_975_);
return v_res_979_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_980_, lean_object* v_as_981_, size_t v_i_982_, size_t v_stop_983_, lean_object* v_b_984_){
_start:
{
lean_object* v___y_986_; uint8_t v___x_990_; 
v___x_990_ = lean_usize_dec_eq(v_i_982_, v_stop_983_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
v___x_991_ = lean_array_uget_borrowed(v_as_981_, v_i_982_);
switch(lean_obj_tag(v___x_991_))
{
case 0:
{
lean_object* v_key_992_; lean_object* v_val_993_; lean_object* v___x_994_; 
v_key_992_ = lean_ctor_get(v___x_991_, 0);
v_val_993_ = lean_ctor_get(v___x_991_, 1);
lean_inc(v_f_980_);
lean_inc(v_val_993_);
lean_inc(v_key_992_);
v___x_994_ = lean_apply_3(v_f_980_, v_b_984_, v_key_992_, v_val_993_);
v___y_986_ = v___x_994_;
goto v___jp_985_;
}
case 1:
{
lean_object* v_node_995_; lean_object* v___x_996_; 
v_node_995_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_f_980_);
v___x_996_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_980_, v_node_995_, v_b_984_);
v___y_986_ = v___x_996_;
goto v___jp_985_;
}
default: 
{
v___y_986_ = v_b_984_;
goto v___jp_985_;
}
}
}
else
{
lean_dec(v_f_980_);
return v_b_984_;
}
v___jp_985_:
{
size_t v___x_987_; size_t v___x_988_; 
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_982_, v___x_987_);
v_i_982_ = v___x_988_;
v_b_984_ = v___y_986_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_980_ = stack[0].m_obj;
lean_object* v_as_981_ = stack[1].m_obj;
size_t v_i_982_ = stack[2].m_num;
size_t v_stop_983_ = stack[3].m_num;
lean_object* v_b_984_ = stack[4].m_obj;
lean_object* v_res_997_;
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_980_, v_as_981_, v_i_982_, v_stop_983_, v_b_984_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v_es_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_es_1001_ = lean_ctor_get(v_x_999_, 0);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_size(v_es_1001_);
v___x_1004_ = lean_nat_dec_lt(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec(v_f_998_);
return v_x_1000_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = lean_usize_of_nat(v___x_1003_);
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_998_, v_es_1001_, v___x_1005_, v___x_1006_, v_x_1000_);
return v___x_1007_;
}
}
else
{
lean_object* v_ks_1008_; lean_object* v_vs_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_ks_1008_ = lean_ctor_get(v_x_999_, 0);
v_vs_1009_ = lean_ctor_get(v_x_999_, 1);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_998_, v_ks_1008_, v_vs_1009_, v___x_1010_, v_x_1000_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1012_, v_x_1013_, v_x_1014_);
lean_dec_ref(v_x_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_1016_, lean_object* v_as_1017_, lean_object* v_i_1018_, lean_object* v_stop_1019_, lean_object* v_b_1020_){
_start:
{
size_t v_i_boxed_1021_; size_t v_stop_boxed_1022_; lean_object* v_res_1023_; 
v_i_boxed_1021_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_stop_boxed_1022_ = lean_unbox_usize(v_stop_1019_);
lean_dec(v_stop_1019_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1016_, v_as_1017_, v_i_boxed_1021_, v_stop_boxed_1022_, v_b_1020_);
lean_dec_ref(v_as_1017_);
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
lean_dec_ref_known(v_x_1040_, 3);
lean_inc(v_f_1038_);
v___x_1044_ = lean_apply_3(v_f_1038_, v_x_1039_, v_key_1041_, v_value_1042_);
v_x_1039_ = v___x_1044_;
v_x_1040_ = v_tail_1043_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1046_, lean_object* v_as_1047_, size_t v_i_1048_, size_t v_stop_1049_, lean_object* v_b_1050_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1046_ = stack[0].m_obj;
lean_object* v_as_1047_ = stack[1].m_obj;
size_t v_i_1048_ = stack[2].m_num;
size_t v_stop_1049_ = stack[3].m_num;
lean_object* v_b_1050_ = stack[4].m_obj;
lean_object* v_res_1057_;
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1046_, v_as_1047_, v_i_1048_, v_stop_1049_, v_b_1050_);
stack->m_obj
 = v_res_1057_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1058_, lean_object* v_as_1059_, lean_object* v_i_1060_, lean_object* v_stop_1061_, lean_object* v_b_1062_){
_start:
{
size_t v_i_boxed_1063_; size_t v_stop_boxed_1064_; lean_object* v_res_1065_; 
v_i_boxed_1063_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_stop_boxed_1064_ = lean_unbox_usize(v_stop_1061_);
lean_dec(v_stop_1061_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1058_, v_as_1059_, v_i_boxed_1063_, v_stop_boxed_1064_, v_b_1062_);
lean_dec_ref(v_as_1059_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1066_, lean_object* v_init_1067_, lean_object* v_m_1068_){
_start:
{
lean_object* v_map_u2081_1069_; lean_object* v_map_u2082_1070_; lean_object* v_buckets_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_map_u2081_1069_ = lean_ctor_get(v_m_1068_, 0);
v_map_u2082_1070_ = lean_ctor_get(v_m_1068_, 1);
v_buckets_1071_ = lean_ctor_get(v_map_u2081_1069_, 1);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_array_get_size(v_buckets_1071_);
v___x_1074_ = lean_nat_dec_lt(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1070_, v_f_1066_, v_init_1067_);
return v___x_1075_;
}
else
{
size_t v___x_1076_; size_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = lean_usize_of_nat(v___x_1073_);
lean_inc(v_f_1066_);
v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1066_, v_buckets_1071_, v___x_1076_, v___x_1077_, v_init_1067_);
v___x_1079_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1070_, v_f_1066_, v___x_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1080_, lean_object* v_init_1081_, lean_object* v_m_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1080_, v_init_1081_, v_m_1082_);
lean_dec_ref(v_m_1082_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1084_, lean_object* v_e_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v_toEnvExtension_1087_; lean_object* v_asyncMode_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1086_ = l_Lean_aliasExtension;
v_toEnvExtension_1087_ = lean_ctor_get(v___x_1086_, 0);
v_asyncMode_1088_ = lean_ctor_get(v_toEnvExtension_1087_, 2);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1089_, 0, v_e_1085_);
v___x_1090_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1090_, v___x_1086_, v_env_1084_, v_asyncMode_1088_, v___x_1092_);
v___x_1094_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1089_, v___x_1091_, v___x_1093_);
lean_dec(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1095_, lean_object* v_00_u03c3_1096_, lean_object* v_f_1097_, lean_object* v_init_1098_, lean_object* v_m_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1097_, v_init_1098_, v_m_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1101_, lean_object* v_00_u03c3_1102_, lean_object* v_f_1103_, lean_object* v_init_1104_, lean_object* v_m_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1101_, v_00_u03c3_1102_, v_f_1103_, v_init_1104_, v_m_1105_);
lean_dec_ref(v_m_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1107_, lean_object* v_00_u03c3_1108_, lean_object* v_f_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_map_1115_, lean_object* v_f_1116_, lean_object* v_init_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1115_, v_f_1116_, v_init_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_map_1121_, lean_object* v_f_1122_, lean_object* v_init_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1119_, v_00_u03b2_1120_, v_map_1121_, v_f_1122_, v_init_1123_);
lean_dec_ref(v_map_1121_);
return v_res_1124_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1125_, lean_object* v_00_u03c3_1126_, lean_object* v_f_1127_, lean_object* v_as_1128_, size_t v_i_1129_, size_t v_stop_1130_, lean_object* v_b_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1127_, v_as_1128_, v_i_1129_, v_stop_1130_, v_b_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1127_ = stack[2].m_obj;
lean_object* v_as_1128_ = stack[3].m_obj;
size_t v_i_1129_ = stack[4].m_num;
size_t v_stop_1130_ = stack[5].m_num;
lean_object* v_b_1131_ = stack[6].m_obj;
lean_object* v_res_1133_;
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_box(0), lean_box(0), v_f_1127_, v_as_1128_, v_i_1129_, v_stop_1130_, v_b_1131_);
stack->m_obj
 = v_res_1133_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1134_, lean_object* v_00_u03c3_1135_, lean_object* v_f_1136_, lean_object* v_as_1137_, lean_object* v_i_1138_, lean_object* v_stop_1139_, lean_object* v_b_1140_){
_start:
{
size_t v_i_boxed_1141_; size_t v_stop_boxed_1142_; lean_object* v_res_1143_; 
v_i_boxed_1141_ = lean_unbox_usize(v_i_1138_);
lean_dec(v_i_1138_);
v_stop_boxed_1142_ = lean_unbox_usize(v_stop_1139_);
lean_dec(v_stop_1139_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1134_, v_00_u03c3_1135_, v_f_1136_, v_as_1137_, v_i_boxed_1141_, v_stop_boxed_1142_, v_b_1140_);
lean_dec_ref(v_as_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1144_, lean_object* v_f_1145_, lean_object* v_init_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1145_, v_map_1144_, v_init_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1148_, lean_object* v_f_1149_, lean_object* v_init_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1148_, v_f_1149_, v_init_1150_);
lean_dec_ref(v_map_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_map_1154_, lean_object* v_f_1155_, lean_object* v_init_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1155_, v_map_1154_, v_init_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_map_1160_, lean_object* v_f_1161_, lean_object* v_init_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1158_, v_00_u03b2_1159_, v_map_1160_, v_f_1161_, v_init_1162_);
lean_dec_ref(v_map_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1164_, lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_f_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1167_, v_x_1168_, v_x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1171_, lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_f_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1171_, v_00_u03b1_1172_, v_00_u03b2_1173_, v_f_1174_, v_x_1175_, v_x_1176_);
lean_dec_ref(v_x_1175_);
return v_res_1177_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_00_u03c3_1180_, lean_object* v_f_1181_, lean_object* v_as_1182_, size_t v_i_1183_, size_t v_stop_1184_, lean_object* v_b_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1181_, v_as_1182_, v_i_1183_, v_stop_1184_, v_b_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1181_ = stack[3].m_obj;
lean_object* v_as_1182_ = stack[4].m_obj;
size_t v_i_1183_ = stack[5].m_num;
size_t v_stop_1184_ = stack[6].m_num;
lean_object* v_b_1185_ = stack[7].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_box(0), lean_box(0), lean_box(0), v_f_1181_, v_as_1182_, v_i_1183_, v_stop_1184_, v_b_1185_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_00_u03b2_1189_, lean_object* v_00_u03c3_1190_, lean_object* v_f_1191_, lean_object* v_as_1192_, lean_object* v_i_1193_, lean_object* v_stop_1194_, lean_object* v_b_1195_){
_start:
{
size_t v_i_boxed_1196_; size_t v_stop_boxed_1197_; lean_object* v_res_1198_; 
v_i_boxed_1196_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_stop_boxed_1197_ = lean_unbox_usize(v_stop_1194_);
lean_dec(v_stop_1194_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1188_, v_00_u03b2_1189_, v_00_u03c3_1190_, v_f_1191_, v_as_1192_, v_i_boxed_1196_, v_stop_boxed_1197_, v_b_1195_);
lean_dec_ref(v_as_1192_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1199_, lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_f_1202_, lean_object* v_keys_1203_, lean_object* v_vals_1204_, lean_object* v_heq_1205_, lean_object* v_i_1206_, lean_object* v_acc_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1202_, v_keys_1203_, v_vals_1204_, v_i_1206_, v_acc_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1209_, lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_f_1212_, lean_object* v_keys_1213_, lean_object* v_vals_1214_, lean_object* v_heq_1215_, lean_object* v_i_1216_, lean_object* v_acc_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1209_, v_00_u03b1_1210_, v_00_u03b2_1211_, v_f_1212_, v_keys_1213_, v_vals_1214_, v_heq_1215_, v_i_1216_, v_acc_1217_);
lean_dec_ref(v_vals_1214_);
lean_dec_ref(v_keys_1213_);
return v_res_1218_;
}
}
uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1219_, lean_object* v_declName_1220_){
_start:
{
uint8_t v___y_1222_; uint8_t v___x_1225_; 
v___x_1225_ = l_Lean_Environment_containsOnBranch(v_env_1219_, v_declName_1220_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
lean_inc(v_declName_1220_);
lean_inc_ref(v_env_1219_);
v___x_1226_ = lean_is_reserved_name(v_env_1219_, v_declName_1220_);
v___y_1222_ = v___x_1226_;
goto v___jp_1221_;
}
else
{
v___y_1222_ = v___x_1225_;
goto v___jp_1221_;
}
v___jp_1221_:
{
if (v___y_1222_ == 0)
{
uint8_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 1;
v___x_1224_ = l_Lean_Environment_contains(v_env_1219_, v_declName_1220_, v___x_1223_);
return v___x_1224_;
}
else
{
lean_dec(v_declName_1220_);
lean_dec_ref(v_env_1219_);
return v___y_1222_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1219_ = stack[0].m_obj;
lean_object* v_declName_1220_ = stack[1].m_obj;
uint8_t v_res_1227_;
v_res_1227_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1219_, v_declName_1220_);
stack->m_num = v_res_1227_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1228_, lean_object* v_declName_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1228_, v_declName_1229_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1232_, lean_object* v_decl_1233_, lean_object* v_ref_1234_){
_start:
{
lean_object* v_defValue_1236_; lean_object* v_descr_1237_; lean_object* v_deprecation_x3f_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_defValue_1236_ = lean_ctor_get(v_decl_1233_, 0);
v_descr_1237_ = lean_ctor_get(v_decl_1233_, 1);
v_deprecation_x3f_1238_ = lean_ctor_get(v_decl_1233_, 2);
v___x_1239_ = lean_alloc_ctor(1, 0, 1);
v___x_1240_ = lean_unbox(v_defValue_1236_);
lean_ctor_set_uint8(v___x_1239_, 0, v___x_1240_);
lean_inc(v_deprecation_x3f_1238_);
lean_inc_ref(v_descr_1237_);
lean_inc_n(v_name_1232_, 2);
v___x_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1241_, 0, v_name_1232_);
lean_ctor_set(v___x_1241_, 1, v_ref_1234_);
lean_ctor_set(v___x_1241_, 2, v___x_1239_);
lean_ctor_set(v___x_1241_, 3, v_descr_1237_);
lean_ctor_set(v___x_1241_, 4, v_deprecation_x3f_1238_);
v___x_1242_ = lean_register_option(v_name_1232_, v___x_1241_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1242_, 0);
lean_dec(v_unused_1251_);
v___x_1244_ = v___x_1242_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v___x_1242_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_inc(v_defValue_1236_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_name_1232_);
lean_ctor_set(v___x_1246_, 1, v_defValue_1236_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_name_1232_);
v_a_1252_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1242_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1242_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1232_ = stack[0].m_obj;
lean_object* v_decl_1233_ = stack[1].m_obj;
lean_object* v_ref_1234_ = stack[2].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1232_, v_decl_1233_, v_ref_1234_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1261_, lean_object* v_decl_1262_, lean_object* v_ref_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1261_, v_decl_1262_, v_ref_1263_);
lean_dec_ref(v_decl_1262_);
return v_res_1265_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1285_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1286_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1287_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1284_, v___x_1285_, v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1288_;
v_res_1288_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
stack->m_obj
 = v_res_1288_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1290_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1310_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1311_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1312_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1309_, v___x_1310_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1313_;
v_res_1313_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1315_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1316_, lean_object* v_opt_1317_){
_start:
{
lean_object* v_name_1318_; lean_object* v_defValue_1319_; lean_object* v_map_1320_; lean_object* v___x_1321_; 
v_name_1318_ = lean_ctor_get(v_opt_1317_, 0);
v_defValue_1319_ = lean_ctor_get(v_opt_1317_, 1);
v_map_1320_ = lean_ctor_get(v_opts_1316_, 0);
v___x_1321_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1320_, v_name_1318_);
if (lean_obj_tag(v___x_1321_) == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_defValue_1319_);
return v___x_1322_;
}
else
{
lean_object* v_val_1323_; 
v_val_1323_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v___x_1321_, 1);
if (lean_obj_tag(v_val_1323_) == 1)
{
uint8_t v_v_1324_; 
v_v_1324_ = lean_ctor_get_uint8(v_val_1323_, 0);
lean_dec_ref_known(v_val_1323_, 0);
return v_v_1324_;
}
else
{
uint8_t v___x_1325_; 
lean_dec(v_val_1323_);
v___x_1325_ = lean_unbox(v_defValue_1319_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1316_ = stack[0].m_obj;
lean_object* v_opt_1317_ = stack[1].m_obj;
uint8_t v_res_1326_;
v_res_1326_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1316_, v_opt_1317_);
stack->m_num = v_res_1326_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1327_, lean_object* v_opt_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1327_, v_opt_1328_);
lean_dec_ref(v_opt_1328_);
lean_dec_ref(v_opts_1327_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1334_, lean_object* v_env_1335_, lean_object* v_as_1336_, size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_b_1339_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1338_, v_sz_1337_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v_env_1335_);
lean_dec(v_declName_1334_);
lean_inc_ref(v_b_1339_);
return v_b_1339_;
}
else
{
lean_object* v_a_1341_; lean_object* v_toImport_1342_; lean_object* v_module_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_a_1341_ = lean_array_uget_borrowed(v_as_1336_, v_i_1338_);
v_toImport_1342_ = lean_ctor_get(v_a_1341_, 0);
v_module_1343_ = lean_ctor_get(v_toImport_1342_, 0);
v___x_1344_ = lean_box(0);
lean_inc(v_declName_1334_);
lean_inc(v_module_1343_);
v___x_1345_ = l_Lean_mkPrivateNameCore(v_module_1343_, v_declName_1334_);
lean_inc(v___x_1345_);
lean_inc_ref(v_env_1335_);
v___x_1346_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1335_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; 
lean_dec(v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1338_, v___x_1348_);
v_i_1338_ = v___x_1349_;
v_b_1339_ = v___x_1347_;
goto _start;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v_env_1335_);
lean_dec(v_declName_1334_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1345_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1344_);
return v___x_1353_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1334_ = stack[0].m_obj;
lean_object* v_env_1335_ = stack[1].m_obj;
lean_object* v_as_1336_ = stack[2].m_obj;
size_t v_sz_1337_ = stack[3].m_num;
size_t v_i_1338_ = stack[4].m_num;
lean_object* v_b_1339_ = stack[5].m_obj;
lean_object* v_res_1354_;
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1334_, v_env_1335_, v_as_1336_, v_sz_1337_, v_i_1338_, v_b_1339_);
stack->m_obj
 = v_res_1354_;
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
lean_dec_ref(v_b_1360_);
lean_dec_ref(v_as_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1364_, lean_object* v_opts_1365_, lean_object* v_declName_1366_){
_start:
{
uint8_t v_isExporting_1382_; 
v_isExporting_1382_ = lean_ctor_get_uint8(v_env_1364_, sizeof(void*)*13);
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
v_isModule_1371_ = lean_ctor_get_uint8(v___x_1370_, sizeof(void*)*8 + 4);
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
v_importAllModules_1373_ = lean_ctor_get(v___x_1370_, 6);
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
lean_dec_ref_known(v_fst_1379_, 1);
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
lean_dec_ref_known(v___x_1399_, 1);
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
lean_dec_ref_known(v_x_1440_, 2);
v_ns_1444_ = lean_ctor_get(v_head_1442_, 0);
lean_inc(v_ns_1444_);
v_except_1445_ = lean_ctor_get(v_head_1442_, 1);
lean_inc(v_except_1445_);
lean_dec_ref_known(v_head_1442_, 2);
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
lean_dec_ref_known(v_head_1442_, 2);
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
lean_dec_ref_known(v___x_1530_, 1);
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
lean_inc_ref_n(v_env_1498_, 2);
v_resolvedIds_1514_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1498_, v_opts_1499_, v_id_1511_, v_openDecls_1501_, v___y_1513_);
v___x_1515_ = l_Lean_Name_isAtomic(v_id_1511_);
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
lean_dec_ref_known(v___x_1526_, 1);
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
v___x_1566_ = lean_panic_fn_borrowed(v___x_1565_, v_msg_1564_);
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
lean_dec_ref_known(v_head_1595_, 2);
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
lean_dec_ref_known(v_x_1593_, 2);
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
lean_dec_ref_known(v___x_1621_, 1);
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
lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1650_, lean_object* v_toPure_1651_, lean_object* v_id_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, uint8_t v_____do__lift_1657_){
_start:
{
uint8_t v_isExporting_1661_; 
v_isExporting_1661_ = lean_ctor_get_uint8(v_____do__lift_1650_, sizeof(void*)*13);
if (v_isExporting_1661_ == 0)
{
lean_dec_ref(v_inst_1656_);
lean_dec(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_inst_1653_);
lean_dec(v_id_1652_);
goto v___jp_1658_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_isPrivateName(v_id_1652_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_inst_1656_);
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
lean_dec_ref(v_inst_1656_);
lean_dec(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_inst_1653_);
lean_dec(v_id_1652_);
goto v___jp_1658_;
}
else
{
lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_toPure_1651_);
v___x_1663_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1664_ = 0;
v___x_1665_ = l_Lean_MessageData_ofConstName(v_id_1652_, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1663_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_logWarning___redArg(v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v___x_1668_);
return v___x_1669_;
}
}
}
v___jp_1658_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_apply_2(v_toPure_1651_, lean_box(0), v___x_1659_);
return v___x_1660_;
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1650_ = stack[0].m_obj;
lean_object* v_toPure_1651_ = stack[1].m_obj;
lean_object* v_id_1652_ = stack[2].m_obj;
lean_object* v_inst_1653_ = stack[3].m_obj;
lean_object* v_inst_1654_ = stack[4].m_obj;
lean_object* v_inst_1655_ = stack[5].m_obj;
lean_object* v_inst_1656_ = stack[6].m_obj;
uint8_t v_____do__lift_1657_ = stack[7].m_num;
lean_object* v_res_1670_;
v_res_1670_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1650_, v_toPure_1651_, v_id_1652_, v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_____do__lift_1657_);
stack->m_obj
 = v_res_1670_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1671_, lean_object* v_toPure_1672_, lean_object* v_id_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_____do__lift_1678_){
_start:
{
uint8_t v_____do__lift_199__boxed_1679_; lean_object* v_res_1680_; 
v_____do__lift_199__boxed_1679_ = lean_unbox(v_____do__lift_1678_);
v_res_1680_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1671_, v_toPure_1672_, v_id_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_____do__lift_199__boxed_1679_);
lean_dec_ref(v_____do__lift_1671_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1681_, lean_object* v_id_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v___x_1687_, lean_object* v_toBind_1688_, lean_object* v_____do__lift_1689_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_inc_ref(v_inst_1686_);
lean_inc_ref(v_inst_1683_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1690_, 0, v_____do__lift_1689_);
lean_closure_set(v___f_1690_, 1, v_toPure_1681_);
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
lean_object* v___x_1700_; lean_object* v_toApplicative_1701_; lean_object* v_toBind_1702_; lean_object* v_getEnv_1703_; lean_object* v_toPure_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; 
v___x_1700_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1701_ = lean_ctor_get(v_inst_1694_, 0);
v_toBind_1702_ = lean_ctor_get(v_inst_1694_, 1);
lean_inc_n(v_toBind_1702_, 2);
v_getEnv_1703_ = lean_ctor_get(v_inst_1695_, 0);
lean_inc(v_getEnv_1703_);
lean_dec_ref(v_inst_1695_);
v_toPure_1704_ = lean_ctor_get(v_toApplicative_1701_, 1);
lean_inc(v_toPure_1704_);
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1705_, 0, v_toPure_1704_);
lean_closure_set(v___f_1705_, 1, v_id_1699_);
lean_closure_set(v___f_1705_, 2, v_inst_1694_);
lean_closure_set(v___f_1705_, 3, v_inst_1697_);
lean_closure_set(v___f_1705_, 4, v_inst_1698_);
lean_closure_set(v___f_1705_, 5, v_inst_1696_);
lean_closure_set(v___f_1705_, 6, v___x_1700_);
lean_closure_set(v___f_1705_, 7, v_toBind_1702_);
v___x_1706_ = lean_apply_4(v_toBind_1702_, lean_box(0), lean_box(0), v_getEnv_1703_, v___f_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_id_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1708_, v_inst_1709_, v_inst_1710_, v_inst_1711_, v_inst_1712_, v_id_1713_);
return v___x_1714_;
}
}
lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1715_, lean_object* v_n_1716_, lean_object* v_toPure_1717_, uint8_t v___y_1718_, uint8_t v___x_1719_, lean_object* v_____r_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1715_, v_n_1716_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_box(v___y_1718_);
v___x_1723_ = lean_apply_2(v_toPure_1717_, lean_box(0), v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v_val_1724_; lean_object* v___x_1725_; uint8_t v_isModule_1726_; 
v_val_1724_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1724_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1725_ = l_Lean_Environment_header(v_env_1715_);
v_isModule_1726_ = lean_ctor_get_uint8(v___x_1725_, sizeof(void*)*8 + 4);
if (v_isModule_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_dec_ref(v___x_1725_);
lean_dec(v_val_1724_);
v___x_1727_ = lean_box(v___x_1719_);
v___x_1728_ = lean_apply_2(v_toPure_1717_, lean_box(0), v___x_1727_);
return v___x_1728_;
}
else
{
lean_object* v_modules_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_modules_1729_ = lean_ctor_get(v___x_1725_, 3);
lean_inc_ref(v_modules_1729_);
lean_dec_ref(v___x_1725_);
v___x_1730_ = lean_array_get_size(v_modules_1729_);
v___x_1731_ = lean_nat_dec_lt(v_val_1724_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v_modules_1729_);
lean_dec(v_val_1724_);
v___x_1732_ = lean_box(v_isModule_1726_);
v___x_1733_ = lean_apply_2(v_toPure_1717_, lean_box(0), v___x_1732_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v_toImport_1735_; uint8_t v_importAll_1736_; 
v___x_1734_ = lean_array_fget(v_modules_1729_, v_val_1724_);
lean_dec(v_val_1724_);
lean_dec_ref(v_modules_1729_);
v_toImport_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_toImport_1735_);
lean_dec(v___x_1734_);
v_importAll_1736_ = lean_ctor_get_uint8(v_toImport_1735_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1735_);
if (v_importAll_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_box(v_isModule_1726_);
v___x_1738_ = lean_apply_2(v_toPure_1717_, lean_box(0), v___x_1737_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_box(v___y_1718_);
v___x_1740_ = lean_apply_2(v_toPure_1717_, lean_box(0), v___x_1739_);
return v___x_1740_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_isInaccessiblePrivateName___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1715_ = stack[0].m_obj;
lean_object* v_n_1716_ = stack[1].m_obj;
lean_object* v_toPure_1717_ = stack[2].m_obj;
uint8_t v___y_1718_ = stack[3].m_num;
uint8_t v___x_1719_ = stack[4].m_num;
lean_object* v_____r_1720_ = stack[5].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1715_, v_n_1716_, v_toPure_1717_, v___y_1718_, v___x_1719_, v_____r_1720_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1742_, lean_object* v_n_1743_, lean_object* v_toPure_1744_, lean_object* v___y_1745_, lean_object* v___x_1746_, lean_object* v_____r_1747_){
_start:
{
uint8_t v___y_386__boxed_1748_; uint8_t v___x_387__boxed_1749_; lean_object* v_res_1750_; 
v___y_386__boxed_1748_ = lean_unbox(v___y_1745_);
v___x_387__boxed_1749_ = lean_unbox(v___x_1746_);
v_res_1750_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1742_, v_n_1743_, v_toPure_1744_, v___y_386__boxed_1748_, v___x_387__boxed_1749_, v_____r_1747_);
lean_dec(v_n_1743_);
lean_dec_ref(v_env_1742_);
return v_res_1750_;
}
}
lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1751_, lean_object* v_n_1752_, lean_object* v_toPure_1753_, uint8_t v___x_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_toBind_1760_, uint8_t v___y_1761_, uint8_t v_____do__lift_1762_){
_start:
{
uint8_t v___y_1764_; uint8_t v_isExporting_1770_; 
v_isExporting_1770_ = lean_ctor_get_uint8(v_env_1751_, sizeof(void*)*13);
if (v_isExporting_1770_ == 0)
{
v___y_1764_ = v___y_1761_;
goto v___jp_1763_;
}
else
{
if (v_____do__lift_1762_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v_toBind_1760_);
lean_dec(v_inst_1759_);
lean_dec_ref(v_inst_1758_);
lean_dec_ref(v_inst_1757_);
lean_dec_ref(v_inst_1756_);
lean_dec_ref(v_inst_1755_);
lean_dec(v_n_1752_);
lean_dec_ref(v_env_1751_);
v___x_1771_ = lean_box(v___x_1754_);
v___x_1772_ = lean_apply_2(v_toPure_1753_, lean_box(0), v___x_1771_);
return v___x_1772_;
}
else
{
v___y_1764_ = v___y_1761_;
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
lean_closure_set(v___f_1767_, 2, v_toPure_1753_);
lean_closure_set(v___f_1767_, 3, v___x_1765_);
lean_closure_set(v___f_1767_, 4, v___x_1766_);
v___x_1768_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1755_, v_inst_1756_, v_inst_1757_, v_inst_1758_, v_inst_1759_, v_n_1752_);
v___x_1769_ = lean_apply_4(v_toBind_1760_, lean_box(0), lean_box(0), v___x_1768_, v___f_1767_);
return v___x_1769_;
}
}
}
LEAN_EXPORT void l_Lean_isInaccessiblePrivateName___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1751_ = stack[0].m_obj;
lean_object* v_n_1752_ = stack[1].m_obj;
lean_object* v_toPure_1753_ = stack[2].m_obj;
uint8_t v___x_1754_ = stack[3].m_num;
lean_object* v_inst_1755_ = stack[4].m_obj;
lean_object* v_inst_1756_ = stack[5].m_obj;
lean_object* v_inst_1757_ = stack[6].m_obj;
lean_object* v_inst_1758_ = stack[7].m_obj;
lean_object* v_inst_1759_ = stack[8].m_obj;
lean_object* v_toBind_1760_ = stack[9].m_obj;
uint8_t v___y_1761_ = stack[10].m_num;
uint8_t v_____do__lift_1762_ = stack[11].m_num;
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1751_, v_n_1752_, v_toPure_1753_, v___x_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v_inst_1758_, v_inst_1759_, v_toBind_1760_, v___y_1761_, v_____do__lift_1762_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1774_, lean_object* v_n_1775_, lean_object* v_toPure_1776_, lean_object* v___x_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_toBind_1783_, lean_object* v___y_1784_, lean_object* v_____do__lift_1785_){
_start:
{
uint8_t v___x_449__boxed_1786_; uint8_t v___y_455__boxed_1787_; uint8_t v_____do__lift_456__boxed_1788_; lean_object* v_res_1789_; 
v___x_449__boxed_1786_ = lean_unbox(v___x_1777_);
v___y_455__boxed_1787_ = lean_unbox(v___y_1784_);
v_____do__lift_456__boxed_1788_ = lean_unbox(v_____do__lift_1785_);
v_res_1789_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1774_, v_n_1775_, v_toPure_1776_, v___x_449__boxed_1786_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_inst_1781_, v_inst_1782_, v_toBind_1783_, v___y_455__boxed_1787_, v_____do__lift_456__boxed_1788_);
return v_res_1789_;
}
}
lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1790_, lean_object* v_toPure_1791_, uint8_t v___x_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_toBind_1798_, uint8_t v___y_1799_, lean_object* v___x_1800_, lean_object* v_env_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1802_ = lean_box(v___x_1792_);
v___x_1803_ = lean_box(v___y_1799_);
lean_inc(v_toBind_1798_);
lean_inc_ref(v_inst_1795_);
lean_inc_ref(v_inst_1793_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1804_, 0, v_env_1801_);
lean_closure_set(v___f_1804_, 1, v_n_1790_);
lean_closure_set(v___f_1804_, 2, v_toPure_1791_);
lean_closure_set(v___f_1804_, 3, v___x_1802_);
lean_closure_set(v___f_1804_, 4, v_inst_1793_);
lean_closure_set(v___f_1804_, 5, v_inst_1794_);
lean_closure_set(v___f_1804_, 6, v_inst_1795_);
lean_closure_set(v___f_1804_, 7, v_inst_1796_);
lean_closure_set(v___f_1804_, 8, v_inst_1797_);
lean_closure_set(v___f_1804_, 9, v_toBind_1798_);
lean_closure_set(v___f_1804_, 10, v___x_1803_);
v___x_1805_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1806_ = l_Lean_Option_getM___redArg(v_inst_1793_, v_inst_1795_, v___x_1800_, v___x_1805_);
v___x_1807_ = lean_apply_4(v_toBind_1798_, lean_box(0), lean_box(0), v___x_1806_, v___f_1804_);
return v___x_1807_;
}
}
LEAN_EXPORT void l_Lean_isInaccessiblePrivateName___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1790_ = stack[0].m_obj;
lean_object* v_toPure_1791_ = stack[1].m_obj;
uint8_t v___x_1792_ = stack[2].m_num;
lean_object* v_inst_1793_ = stack[3].m_obj;
lean_object* v_inst_1794_ = stack[4].m_obj;
lean_object* v_inst_1795_ = stack[5].m_obj;
lean_object* v_inst_1796_ = stack[6].m_obj;
lean_object* v_inst_1797_ = stack[7].m_obj;
lean_object* v_toBind_1798_ = stack[8].m_obj;
uint8_t v___y_1799_ = stack[9].m_num;
lean_object* v___x_1800_ = stack[10].m_obj;
lean_object* v_env_1801_ = stack[11].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1790_, v_toPure_1791_, v___x_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_inst_1797_, v_toBind_1798_, v___y_1799_, v___x_1800_, v_env_1801_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1809_, lean_object* v_toPure_1810_, lean_object* v___x_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_toBind_1817_, lean_object* v___y_1818_, lean_object* v___x_1819_, lean_object* v_env_1820_){
_start:
{
uint8_t v___x_516__boxed_1821_; uint8_t v___y_522__boxed_1822_; lean_object* v_res_1823_; 
v___x_516__boxed_1821_ = lean_unbox(v___x_1811_);
v___y_522__boxed_1822_ = lean_unbox(v___y_1818_);
v_res_1823_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1809_, v_toPure_1810_, v___x_516__boxed_1821_, v_inst_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v_inst_1816_, v_toBind_1817_, v___y_522__boxed_1822_, v___x_1819_, v_env_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_n_1829_){
_start:
{
lean_object* v___x_1830_; uint8_t v___y_1832_; uint8_t v___x_1847_; 
v___x_1830_ = l_Lean_KVMap_instValueBool;
v___x_1847_ = l_Lean_isPrivateName(v_n_1829_);
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = 1;
v___y_1832_ = v___x_1848_;
goto v___jp_1831_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = 0;
v___y_1832_ = v___x_1849_;
goto v___jp_1831_;
}
v___jp_1831_:
{
if (v___y_1832_ == 0)
{
lean_object* v_toApplicative_1833_; lean_object* v_toBind_1834_; lean_object* v_toPure_1835_; lean_object* v_getEnv_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___x_1841_; 
v_toApplicative_1833_ = lean_ctor_get(v_inst_1826_, 0);
v_toBind_1834_ = lean_ctor_get(v_inst_1826_, 1);
lean_inc_n(v_toBind_1834_, 2);
v_toPure_1835_ = lean_ctor_get(v_toApplicative_1833_, 1);
lean_inc(v_toPure_1835_);
v_getEnv_1836_ = lean_ctor_get(v_inst_1827_, 0);
lean_inc(v_getEnv_1836_);
v___x_1837_ = 1;
v___x_1838_ = lean_box(v___x_1837_);
v___x_1839_ = lean_box(v___y_1832_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1840_, 0, v_n_1829_);
lean_closure_set(v___f_1840_, 1, v_toPure_1835_);
lean_closure_set(v___f_1840_, 2, v___x_1838_);
lean_closure_set(v___f_1840_, 3, v_inst_1826_);
lean_closure_set(v___f_1840_, 4, v_inst_1827_);
lean_closure_set(v___f_1840_, 5, v_inst_1828_);
lean_closure_set(v___f_1840_, 6, v_inst_1824_);
lean_closure_set(v___f_1840_, 7, v_inst_1825_);
lean_closure_set(v___f_1840_, 8, v_toBind_1834_);
lean_closure_set(v___f_1840_, 9, v___x_1839_);
lean_closure_set(v___f_1840_, 10, v___x_1830_);
v___x_1841_ = lean_apply_4(v_toBind_1834_, lean_box(0), lean_box(0), v_getEnv_1836_, v___f_1840_);
return v___x_1841_;
}
else
{
lean_object* v_toApplicative_1842_; lean_object* v_toPure_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_toApplicative_1842_ = lean_ctor_get(v_inst_1826_, 0);
lean_inc_ref(v_toApplicative_1842_);
lean_dec(v_n_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec_ref(v_inst_1826_);
lean_dec(v_inst_1825_);
lean_dec_ref(v_inst_1824_);
v_toPure_1843_ = lean_ctor_get(v_toApplicative_1842_, 1);
lean_inc(v_toPure_1843_);
lean_dec_ref(v_toApplicative_1842_);
v___x_1844_ = 0;
v___x_1845_ = lean_box(v___x_1844_);
v___x_1846_ = lean_apply_2(v_toPure_1843_, lean_box(0), v___x_1845_);
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_n_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1851_, v_inst_1852_, v_inst_1853_, v_inst_1854_, v_inst_1855_, v_n_1856_);
return v___x_1857_;
}
}
uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1858_){
_start:
{
lean_object* v_fst_1859_; uint8_t v___x_1860_; 
v_fst_1859_ = lean_ctor_get(v_x_1858_, 0);
v___x_1860_ = l_Lean_isPrivateName(v_fst_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1858_ = stack[0].m_obj;
uint8_t v_res_1861_;
v_res_1861_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1858_);
stack->m_num = v_res_1861_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1862_){
_start:
{
uint8_t v_res_1863_; lean_object* v_r_1864_; 
v_res_1863_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1862_);
lean_dec_ref(v_x_1862_);
v_r_1864_ = lean_box(v_res_1863_);
return v_r_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1865_, lean_object* v_res_1866_, lean_object* v_____r_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_apply_2(v_toPure_1865_, lean_box(0), v_res_1866_);
return v___x_1868_;
}
}
lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1869_, lean_object* v_toPure_1870_, lean_object* v_res_1871_, lean_object* v___f_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_toBind_1878_, lean_object* v___f_1879_, lean_object* v_____do__lift_1880_){
_start:
{
if (v_enableLog_1869_ == 0)
{
lean_object* v___x_1881_; 
lean_dec(v___f_1879_);
lean_dec(v_toBind_1878_);
lean_dec(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
lean_dec_ref(v_inst_1875_);
lean_dec_ref(v_inst_1874_);
lean_dec_ref(v_inst_1873_);
lean_dec_ref(v___f_1872_);
v___x_1881_ = lean_apply_2(v_toPure_1870_, lean_box(0), v_res_1871_);
return v___x_1881_;
}
else
{
uint8_t v_isExporting_1882_; 
v_isExporting_1882_ = lean_ctor_get_uint8(v_____do__lift_1880_, sizeof(void*)*13);
if (v_isExporting_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_dec(v___f_1879_);
lean_dec(v_toBind_1878_);
lean_dec(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
lean_dec_ref(v_inst_1875_);
lean_dec_ref(v_inst_1874_);
lean_dec_ref(v_inst_1873_);
lean_dec_ref(v___f_1872_);
v___x_1883_ = lean_apply_2(v_toPure_1870_, lean_box(0), v_res_1871_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; 
lean_inc(v_res_1871_);
v___x_1884_ = l_List_find_x3f___redArg(v___f_1872_, v_res_1871_);
if (lean_obj_tag(v___x_1884_) == 1)
{
lean_object* v_val_1885_; lean_object* v_fst_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v_res_1871_);
lean_dec(v_toPure_1870_);
v_val_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v_fst_1886_ = lean_ctor_get(v_val_1885_, 0);
lean_inc(v_fst_1886_);
lean_dec(v_val_1885_);
v___x_1887_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1873_, v_inst_1874_, v_inst_1875_, v_inst_1876_, v_inst_1877_, v_fst_1886_);
v___x_1888_ = lean_apply_4(v_toBind_1878_, lean_box(0), lean_box(0), v___x_1887_, v___f_1879_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; 
lean_dec(v___x_1884_);
lean_dec(v___f_1879_);
lean_dec(v_toBind_1878_);
lean_dec(v_inst_1877_);
lean_dec_ref(v_inst_1876_);
lean_dec_ref(v_inst_1875_);
lean_dec_ref(v_inst_1874_);
lean_dec_ref(v_inst_1873_);
v___x_1889_ = lean_apply_2(v_toPure_1870_, lean_box(0), v_res_1871_);
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_enableLog_1869_ = stack[0].m_num;
lean_object* v_toPure_1870_ = stack[1].m_obj;
lean_object* v_res_1871_ = stack[2].m_obj;
lean_object* v___f_1872_ = stack[3].m_obj;
lean_object* v_inst_1873_ = stack[4].m_obj;
lean_object* v_inst_1874_ = stack[5].m_obj;
lean_object* v_inst_1875_ = stack[6].m_obj;
lean_object* v_inst_1876_ = stack[7].m_obj;
lean_object* v_inst_1877_ = stack[8].m_obj;
lean_object* v_toBind_1878_ = stack[9].m_obj;
lean_object* v___f_1879_ = stack[10].m_obj;
lean_object* v_____do__lift_1880_ = stack[11].m_obj;
lean_object* v_res_1890_;
v_res_1890_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_1869_, v_toPure_1870_, v_res_1871_, v___f_1872_, v_inst_1873_, v_inst_1874_, v_inst_1875_, v_inst_1876_, v_inst_1877_, v_toBind_1878_, v___f_1879_, v_____do__lift_1880_);
stack->m_obj
 = v_res_1890_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1891_, lean_object* v_toPure_1892_, lean_object* v_res_1893_, lean_object* v___f_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_toBind_1900_, lean_object* v___f_1901_, lean_object* v_____do__lift_1902_){
_start:
{
uint8_t v_enableLog_boxed_1903_; lean_object* v_res_1904_; 
v_enableLog_boxed_1903_ = lean_unbox(v_enableLog_1891_);
v_res_1904_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1903_, v_toPure_1892_, v_res_1893_, v___f_1894_, v_inst_1895_, v_inst_1896_, v_inst_1897_, v_inst_1898_, v_inst_1899_, v_toBind_1900_, v___f_1901_, v_____do__lift_1902_);
lean_dec_ref(v_____do__lift_1902_);
return v_res_1904_;
}
}
lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1905_, lean_object* v_____do__lift_1906_, lean_object* v_____do__lift_1907_, lean_object* v_id_1908_, lean_object* v_toPure_1909_, uint8_t v_enableLog_1910_, lean_object* v___f_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v_toBind_1917_, lean_object* v_getEnv_1918_, lean_object* v_____do__lift_1919_){
_start:
{
lean_object* v_res_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; 
v_res_1920_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1905_, v_____do__lift_1906_, v_____do__lift_1907_, v_____do__lift_1919_, v_id_1908_);
lean_inc(v_res_1920_);
lean_inc(v_toPure_1909_);
v___f_1921_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1921_, 0, v_toPure_1909_);
lean_closure_set(v___f_1921_, 1, v_res_1920_);
v___x_1922_ = lean_box(v_enableLog_1910_);
lean_inc(v_toBind_1917_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1923_, 0, v___x_1922_);
lean_closure_set(v___f_1923_, 1, v_toPure_1909_);
lean_closure_set(v___f_1923_, 2, v_res_1920_);
lean_closure_set(v___f_1923_, 3, v___f_1911_);
lean_closure_set(v___f_1923_, 4, v_inst_1912_);
lean_closure_set(v___f_1923_, 5, v_inst_1913_);
lean_closure_set(v___f_1923_, 6, v_inst_1914_);
lean_closure_set(v___f_1923_, 7, v_inst_1915_);
lean_closure_set(v___f_1923_, 8, v_inst_1916_);
lean_closure_set(v___f_1923_, 9, v_toBind_1917_);
lean_closure_set(v___f_1923_, 10, v___f_1921_);
v___x_1924_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v_getEnv_1918_, v___f_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1905_ = stack[0].m_obj;
lean_object* v_____do__lift_1906_ = stack[1].m_obj;
lean_object* v_____do__lift_1907_ = stack[2].m_obj;
lean_object* v_id_1908_ = stack[3].m_obj;
lean_object* v_toPure_1909_ = stack[4].m_obj;
uint8_t v_enableLog_1910_ = stack[5].m_num;
lean_object* v___f_1911_ = stack[6].m_obj;
lean_object* v_inst_1912_ = stack[7].m_obj;
lean_object* v_inst_1913_ = stack[8].m_obj;
lean_object* v_inst_1914_ = stack[9].m_obj;
lean_object* v_inst_1915_ = stack[10].m_obj;
lean_object* v_inst_1916_ = stack[11].m_obj;
lean_object* v_toBind_1917_ = stack[12].m_obj;
lean_object* v_getEnv_1918_ = stack[13].m_obj;
lean_object* v_____do__lift_1919_ = stack[14].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1905_, v_____do__lift_1906_, v_____do__lift_1907_, v_id_1908_, v_toPure_1909_, v_enableLog_1910_, v___f_1911_, v_inst_1912_, v_inst_1913_, v_inst_1914_, v_inst_1915_, v_inst_1916_, v_toBind_1917_, v_getEnv_1918_, v_____do__lift_1919_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1926_, lean_object* v_____do__lift_1927_, lean_object* v_____do__lift_1928_, lean_object* v_id_1929_, lean_object* v_toPure_1930_, lean_object* v_enableLog_1931_, lean_object* v___f_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_toBind_1938_, lean_object* v_getEnv_1939_, lean_object* v_____do__lift_1940_){
_start:
{
uint8_t v_enableLog_boxed_1941_; lean_object* v_res_1942_; 
v_enableLog_boxed_1941_ = lean_unbox(v_enableLog_1931_);
v_res_1942_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1926_, v_____do__lift_1927_, v_____do__lift_1928_, v_id_1929_, v_toPure_1930_, v_enableLog_boxed_1941_, v___f_1932_, v_inst_1933_, v_inst_1934_, v_inst_1935_, v_inst_1936_, v_inst_1937_, v_toBind_1938_, v_getEnv_1939_, v_____do__lift_1940_);
lean_dec_ref(v_____do__lift_1927_);
return v_res_1942_;
}
}
lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1943_, lean_object* v_____do__lift_1944_, lean_object* v_id_1945_, lean_object* v_toPure_1946_, uint8_t v_enableLog_1947_, lean_object* v___f_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_toBind_1954_, lean_object* v_getEnv_1955_, lean_object* v_getOpenDecls_1956_, lean_object* v_____do__lift_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___f_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_box(v_enableLog_1947_);
lean_inc(v_toBind_1954_);
v___f_1959_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1959_, 0, v_____do__lift_1943_);
lean_closure_set(v___f_1959_, 1, v_____do__lift_1944_);
lean_closure_set(v___f_1959_, 2, v_____do__lift_1957_);
lean_closure_set(v___f_1959_, 3, v_id_1945_);
lean_closure_set(v___f_1959_, 4, v_toPure_1946_);
lean_closure_set(v___f_1959_, 5, v___x_1958_);
lean_closure_set(v___f_1959_, 6, v___f_1948_);
lean_closure_set(v___f_1959_, 7, v_inst_1949_);
lean_closure_set(v___f_1959_, 8, v_inst_1950_);
lean_closure_set(v___f_1959_, 9, v_inst_1951_);
lean_closure_set(v___f_1959_, 10, v_inst_1952_);
lean_closure_set(v___f_1959_, 11, v_inst_1953_);
lean_closure_set(v___f_1959_, 12, v_toBind_1954_);
lean_closure_set(v___f_1959_, 13, v_getEnv_1955_);
v___x_1960_ = lean_apply_4(v_toBind_1954_, lean_box(0), lean_box(0), v_getOpenDecls_1956_, v___f_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1943_ = stack[0].m_obj;
lean_object* v_____do__lift_1944_ = stack[1].m_obj;
lean_object* v_id_1945_ = stack[2].m_obj;
lean_object* v_toPure_1946_ = stack[3].m_obj;
uint8_t v_enableLog_1947_ = stack[4].m_num;
lean_object* v___f_1948_ = stack[5].m_obj;
lean_object* v_inst_1949_ = stack[6].m_obj;
lean_object* v_inst_1950_ = stack[7].m_obj;
lean_object* v_inst_1951_ = stack[8].m_obj;
lean_object* v_inst_1952_ = stack[9].m_obj;
lean_object* v_inst_1953_ = stack[10].m_obj;
lean_object* v_toBind_1954_ = stack[11].m_obj;
lean_object* v_getEnv_1955_ = stack[12].m_obj;
lean_object* v_getOpenDecls_1956_ = stack[13].m_obj;
lean_object* v_____do__lift_1957_ = stack[14].m_obj;
lean_object* v_res_1961_;
v_res_1961_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1943_, v_____do__lift_1944_, v_id_1945_, v_toPure_1946_, v_enableLog_1947_, v___f_1948_, v_inst_1949_, v_inst_1950_, v_inst_1951_, v_inst_1952_, v_inst_1953_, v_toBind_1954_, v_getEnv_1955_, v_getOpenDecls_1956_, v_____do__lift_1957_);
stack->m_obj
 = v_res_1961_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1962_, lean_object* v_____do__lift_1963_, lean_object* v_id_1964_, lean_object* v_toPure_1965_, lean_object* v_enableLog_1966_, lean_object* v___f_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_toBind_1973_, lean_object* v_getEnv_1974_, lean_object* v_getOpenDecls_1975_, lean_object* v_____do__lift_1976_){
_start:
{
uint8_t v_enableLog_boxed_1977_; lean_object* v_res_1978_; 
v_enableLog_boxed_1977_ = lean_unbox(v_enableLog_1966_);
v_res_1978_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1962_, v_____do__lift_1963_, v_id_1964_, v_toPure_1965_, v_enableLog_boxed_1977_, v___f_1967_, v_inst_1968_, v_inst_1969_, v_inst_1970_, v_inst_1971_, v_inst_1972_, v_toBind_1973_, v_getEnv_1974_, v_getOpenDecls_1975_, v_____do__lift_1976_);
return v_res_1978_;
}
}
lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1979_, lean_object* v_____do__lift_1980_, lean_object* v_id_1981_, lean_object* v_toPure_1982_, uint8_t v_enableLog_1983_, lean_object* v___f_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_toBind_1990_, lean_object* v_getEnv_1991_, lean_object* v_____do__lift_1992_){
_start:
{
lean_object* v_getCurrNamespace_1993_; lean_object* v_getOpenDecls_1994_; lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v_getCurrNamespace_1993_ = lean_ctor_get(v_inst_1979_, 0);
lean_inc(v_getCurrNamespace_1993_);
v_getOpenDecls_1994_ = lean_ctor_get(v_inst_1979_, 1);
lean_inc(v_getOpenDecls_1994_);
lean_dec_ref(v_inst_1979_);
v___x_1995_ = lean_box(v_enableLog_1983_);
lean_inc(v_toBind_1990_);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1996_, 0, v_____do__lift_1980_);
lean_closure_set(v___f_1996_, 1, v_____do__lift_1992_);
lean_closure_set(v___f_1996_, 2, v_id_1981_);
lean_closure_set(v___f_1996_, 3, v_toPure_1982_);
lean_closure_set(v___f_1996_, 4, v___x_1995_);
lean_closure_set(v___f_1996_, 5, v___f_1984_);
lean_closure_set(v___f_1996_, 6, v_inst_1985_);
lean_closure_set(v___f_1996_, 7, v_inst_1986_);
lean_closure_set(v___f_1996_, 8, v_inst_1987_);
lean_closure_set(v___f_1996_, 9, v_inst_1988_);
lean_closure_set(v___f_1996_, 10, v_inst_1989_);
lean_closure_set(v___f_1996_, 11, v_toBind_1990_);
lean_closure_set(v___f_1996_, 12, v_getEnv_1991_);
lean_closure_set(v___f_1996_, 13, v_getOpenDecls_1994_);
v___x_1997_ = lean_apply_4(v_toBind_1990_, lean_box(0), lean_box(0), v_getCurrNamespace_1993_, v___f_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1979_ = stack[0].m_obj;
lean_object* v_____do__lift_1980_ = stack[1].m_obj;
lean_object* v_id_1981_ = stack[2].m_obj;
lean_object* v_toPure_1982_ = stack[3].m_obj;
uint8_t v_enableLog_1983_ = stack[4].m_num;
lean_object* v___f_1984_ = stack[5].m_obj;
lean_object* v_inst_1985_ = stack[6].m_obj;
lean_object* v_inst_1986_ = stack[7].m_obj;
lean_object* v_inst_1987_ = stack[8].m_obj;
lean_object* v_inst_1988_ = stack[9].m_obj;
lean_object* v_inst_1989_ = stack[10].m_obj;
lean_object* v_toBind_1990_ = stack[11].m_obj;
lean_object* v_getEnv_1991_ = stack[12].m_obj;
lean_object* v_____do__lift_1992_ = stack[13].m_obj;
lean_object* v_res_1998_;
v_res_1998_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1979_, v_____do__lift_1980_, v_id_1981_, v_toPure_1982_, v_enableLog_1983_, v___f_1984_, v_inst_1985_, v_inst_1986_, v_inst_1987_, v_inst_1988_, v_inst_1989_, v_toBind_1990_, v_getEnv_1991_, v_____do__lift_1992_);
stack->m_obj
 = v_res_1998_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1999_, lean_object* v_____do__lift_2000_, lean_object* v_id_2001_, lean_object* v_toPure_2002_, lean_object* v_enableLog_2003_, lean_object* v___f_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_toBind_2010_, lean_object* v_getEnv_2011_, lean_object* v_____do__lift_2012_){
_start:
{
uint8_t v_enableLog_boxed_2013_; lean_object* v_res_2014_; 
v_enableLog_boxed_2013_ = lean_unbox(v_enableLog_2003_);
v_res_2014_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1999_, v_____do__lift_2000_, v_id_2001_, v_toPure_2002_, v_enableLog_boxed_2013_, v___f_2004_, v_inst_2005_, v_inst_2006_, v_inst_2007_, v_inst_2008_, v_inst_2009_, v_toBind_2010_, v_getEnv_2011_, v_____do__lift_2012_);
return v_res_2014_;
}
}
lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_id_2017_, lean_object* v_toPure_2018_, uint8_t v_enableLog_2019_, lean_object* v___f_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_toBind_2025_, lean_object* v_getEnv_2026_, lean_object* v_____do__lift_2027_){
_start:
{
lean_object* v_getOptions_2028_; lean_object* v___x_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; 
v_getOptions_2028_ = lean_ctor_get(v_inst_2015_, 0);
lean_inc(v_getOptions_2028_);
v___x_2029_ = lean_box(v_enableLog_2019_);
lean_inc(v_toBind_2025_);
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_2030_, 0, v_inst_2016_);
lean_closure_set(v___f_2030_, 1, v_____do__lift_2027_);
lean_closure_set(v___f_2030_, 2, v_id_2017_);
lean_closure_set(v___f_2030_, 3, v_toPure_2018_);
lean_closure_set(v___f_2030_, 4, v___x_2029_);
lean_closure_set(v___f_2030_, 5, v___f_2020_);
lean_closure_set(v___f_2030_, 6, v_inst_2021_);
lean_closure_set(v___f_2030_, 7, v_inst_2022_);
lean_closure_set(v___f_2030_, 8, v_inst_2015_);
lean_closure_set(v___f_2030_, 9, v_inst_2023_);
lean_closure_set(v___f_2030_, 10, v_inst_2024_);
lean_closure_set(v___f_2030_, 11, v_toBind_2025_);
lean_closure_set(v___f_2030_, 12, v_getEnv_2026_);
v___x_2031_ = lean_apply_4(v_toBind_2025_, lean_box(0), lean_box(0), v_getOptions_2028_, v___f_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2015_ = stack[0].m_obj;
lean_object* v_inst_2016_ = stack[1].m_obj;
lean_object* v_id_2017_ = stack[2].m_obj;
lean_object* v_toPure_2018_ = stack[3].m_obj;
uint8_t v_enableLog_2019_ = stack[4].m_num;
lean_object* v___f_2020_ = stack[5].m_obj;
lean_object* v_inst_2021_ = stack[6].m_obj;
lean_object* v_inst_2022_ = stack[7].m_obj;
lean_object* v_inst_2023_ = stack[8].m_obj;
lean_object* v_inst_2024_ = stack[9].m_obj;
lean_object* v_toBind_2025_ = stack[10].m_obj;
lean_object* v_getEnv_2026_ = stack[11].m_obj;
lean_object* v_____do__lift_2027_ = stack[12].m_obj;
lean_object* v_res_2032_;
v_res_2032_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2015_, v_inst_2016_, v_id_2017_, v_toPure_2018_, v_enableLog_2019_, v___f_2020_, v_inst_2021_, v_inst_2022_, v_inst_2023_, v_inst_2024_, v_toBind_2025_, v_getEnv_2026_, v_____do__lift_2027_);
stack->m_obj
 = v_res_2032_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_id_2035_, lean_object* v_toPure_2036_, lean_object* v_enableLog_2037_, lean_object* v___f_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_toBind_2043_, lean_object* v_getEnv_2044_, lean_object* v_____do__lift_2045_){
_start:
{
uint8_t v_enableLog_boxed_2046_; lean_object* v_res_2047_; 
v_enableLog_boxed_2046_ = lean_unbox(v_enableLog_2037_);
v_res_2047_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2033_, v_inst_2034_, v_id_2035_, v_toPure_2036_, v_enableLog_boxed_2046_, v___f_2038_, v_inst_2039_, v_inst_2040_, v_inst_2041_, v_inst_2042_, v_toBind_2043_, v_getEnv_2044_, v_____do__lift_2045_);
return v_res_2047_;
}
}
lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_id_2055_, uint8_t v_enableLog_2056_){
_start:
{
lean_object* v_toApplicative_2057_; lean_object* v_toBind_2058_; lean_object* v_getEnv_2059_; lean_object* v_toPure_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; 
v_toApplicative_2057_ = lean_ctor_get(v_inst_2049_, 0);
v_toBind_2058_ = lean_ctor_get(v_inst_2049_, 1);
lean_inc_n(v_toBind_2058_, 2);
v_getEnv_2059_ = lean_ctor_get(v_inst_2051_, 0);
lean_inc_n(v_getEnv_2059_, 2);
v_toPure_2060_ = lean_ctor_get(v_toApplicative_2057_, 1);
lean_inc(v_toPure_2060_);
v___f_2061_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2062_ = lean_box(v_enableLog_2056_);
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2063_, 0, v_inst_2052_);
lean_closure_set(v___f_2063_, 1, v_inst_2050_);
lean_closure_set(v___f_2063_, 2, v_id_2055_);
lean_closure_set(v___f_2063_, 3, v_toPure_2060_);
lean_closure_set(v___f_2063_, 4, v___x_2062_);
lean_closure_set(v___f_2063_, 5, v___f_2061_);
lean_closure_set(v___f_2063_, 6, v_inst_2049_);
lean_closure_set(v___f_2063_, 7, v_inst_2051_);
lean_closure_set(v___f_2063_, 8, v_inst_2053_);
lean_closure_set(v___f_2063_, 9, v_inst_2054_);
lean_closure_set(v___f_2063_, 10, v_toBind_2058_);
lean_closure_set(v___f_2063_, 11, v_getEnv_2059_);
v___x_2064_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v_getEnv_2059_, v___f_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2049_ = stack[0].m_obj;
lean_object* v_inst_2050_ = stack[1].m_obj;
lean_object* v_inst_2051_ = stack[2].m_obj;
lean_object* v_inst_2052_ = stack[3].m_obj;
lean_object* v_inst_2053_ = stack[4].m_obj;
lean_object* v_inst_2054_ = stack[5].m_obj;
lean_object* v_id_2055_ = stack[6].m_obj;
uint8_t v_enableLog_2056_ = stack[7].m_num;
lean_object* v_res_2065_;
v_res_2065_ = l_Lean_resolveGlobalName___redArg(v_inst_2049_, v_inst_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v_id_2055_, v_enableLog_2056_);
stack->m_obj
 = v_res_2065_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_id_2072_, lean_object* v_enableLog_2073_){
_start:
{
uint8_t v_enableLog_boxed_2074_; lean_object* v_res_2075_; 
v_enableLog_boxed_2074_ = lean_unbox(v_enableLog_2073_);
v_res_2075_ = l_Lean_resolveGlobalName___redArg(v_inst_2066_, v_inst_2067_, v_inst_2068_, v_inst_2069_, v_inst_2070_, v_inst_2071_, v_id_2072_, v_enableLog_boxed_2074_);
return v_res_2075_;
}
}
lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_id_2083_, uint8_t v_enableLog_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_resolveGlobalName___redArg(v_inst_2077_, v_inst_2078_, v_inst_2079_, v_inst_2080_, v_inst_2081_, v_inst_2082_, v_id_2083_, v_enableLog_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2077_ = stack[1].m_obj;
lean_object* v_inst_2078_ = stack[2].m_obj;
lean_object* v_inst_2079_ = stack[3].m_obj;
lean_object* v_inst_2080_ = stack[4].m_obj;
lean_object* v_inst_2081_ = stack[5].m_obj;
lean_object* v_inst_2082_ = stack[6].m_obj;
lean_object* v_id_2083_ = stack[7].m_obj;
uint8_t v_enableLog_2084_ = stack[8].m_num;
lean_object* v_res_2086_;
v_res_2086_ = l_Lean_resolveGlobalName(lean_box(0), v_inst_2077_, v_inst_2078_, v_inst_2079_, v_inst_2080_, v_inst_2081_, v_inst_2082_, v_id_2083_, v_enableLog_2084_);
stack->m_obj
 = v_res_2086_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_id_2094_, lean_object* v_enableLog_2095_){
_start:
{
uint8_t v_enableLog_boxed_2096_; lean_object* v_res_2097_; 
v_enableLog_boxed_2096_ = lean_unbox(v_enableLog_2095_);
v_res_2097_ = l_Lean_resolveGlobalName(v_m_2087_, v_inst_2088_, v_inst_2089_, v_inst_2090_, v_inst_2091_, v_inst_2092_, v_inst_2093_, v_id_2094_, v_enableLog_boxed_2096_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2098_, lean_object* v_nss_2099_, lean_object* v_____r_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_apply_2(v_toPure_2098_, lean_box(0), v_nss_2099_);
return v___x_2101_;
}
}
lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2104_, lean_object* v_____do__lift_2105_, lean_object* v_id_2106_, uint8_t v_allowEmpty_2107_, lean_object* v_toPure_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_toBind_2111_, lean_object* v_____do__lift_2112_){
_start:
{
lean_object* v_nss_2113_; 
lean_inc(v_id_2106_);
v_nss_2113_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2104_, v_____do__lift_2105_, v_____do__lift_2112_, v_id_2106_);
if (v_allowEmpty_2107_ == 0)
{
uint8_t v___x_2114_; 
v___x_2114_ = l_List_isEmpty___redArg(v_nss_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_dec(v_toBind_2111_);
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
lean_dec(v_id_2106_);
v___x_2115_ = lean_apply_2(v_toPure_2108_, lean_box(0), v_nss_2113_);
return v___x_2115_;
}
else
{
lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___f_2116_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2116_, 0, v_toPure_2108_);
lean_closure_set(v___f_2116_, 1, v_nss_2113_);
v___x_2117_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2118_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2106_, v___x_2114_);
v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2121_ = lean_string_append(v___x_2119_, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = l_Lean_MessageData_ofFormat(v___x_2122_);
v___x_2124_ = l_Lean_throwError___redArg(v_inst_2109_, v_inst_2110_, v___x_2123_);
v___x_2125_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2124_, v___f_2116_);
return v___x_2125_;
}
}
else
{
lean_object* v___x_2126_; 
lean_dec(v_toBind_2111_);
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
lean_dec(v_id_2106_);
v___x_2126_ = lean_apply_2(v_toPure_2108_, lean_box(0), v_nss_2113_);
return v___x_2126_;
}
}
}
LEAN_EXPORT void l_Lean_resolveNamespaceCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_2104_ = stack[0].m_obj;
lean_object* v_____do__lift_2105_ = stack[1].m_obj;
lean_object* v_id_2106_ = stack[2].m_obj;
uint8_t v_allowEmpty_2107_ = stack[3].m_num;
lean_object* v_toPure_2108_ = stack[4].m_obj;
lean_object* v_inst_2109_ = stack[5].m_obj;
lean_object* v_inst_2110_ = stack[6].m_obj;
lean_object* v_toBind_2111_ = stack[7].m_obj;
lean_object* v_____do__lift_2112_ = stack[8].m_obj;
lean_object* v_res_2127_;
v_res_2127_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2104_, v_____do__lift_2105_, v_id_2106_, v_allowEmpty_2107_, v_toPure_2108_, v_inst_2109_, v_inst_2110_, v_toBind_2111_, v_____do__lift_2112_);
stack->m_obj
 = v_res_2127_;
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2128_, lean_object* v_____do__lift_2129_, lean_object* v_id_2130_, lean_object* v_allowEmpty_2131_, lean_object* v_toPure_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_toBind_2135_, lean_object* v_____do__lift_2136_){
_start:
{
uint8_t v_allowEmpty_boxed_2137_; lean_object* v_res_2138_; 
v_allowEmpty_boxed_2137_ = lean_unbox(v_allowEmpty_2131_);
v_res_2138_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2128_, v_____do__lift_2129_, v_id_2130_, v_allowEmpty_boxed_2137_, v_toPure_2132_, v_inst_2133_, v_inst_2134_, v_toBind_2135_, v_____do__lift_2136_);
return v_res_2138_;
}
}
lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2139_, lean_object* v_id_2140_, uint8_t v_allowEmpty_2141_, lean_object* v_toPure_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_toBind_2145_, lean_object* v_getOpenDecls_2146_, lean_object* v_____do__lift_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(v_allowEmpty_2141_);
lean_inc(v_toBind_2145_);
v___f_2149_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2149_, 0, v_____do__lift_2139_);
lean_closure_set(v___f_2149_, 1, v_____do__lift_2147_);
lean_closure_set(v___f_2149_, 2, v_id_2140_);
lean_closure_set(v___f_2149_, 3, v___x_2148_);
lean_closure_set(v___f_2149_, 4, v_toPure_2142_);
lean_closure_set(v___f_2149_, 5, v_inst_2143_);
lean_closure_set(v___f_2149_, 6, v_inst_2144_);
lean_closure_set(v___f_2149_, 7, v_toBind_2145_);
v___x_2150_ = lean_apply_4(v_toBind_2145_, lean_box(0), lean_box(0), v_getOpenDecls_2146_, v___f_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT void l_Lean_resolveNamespaceCore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_2139_ = stack[0].m_obj;
lean_object* v_id_2140_ = stack[1].m_obj;
uint8_t v_allowEmpty_2141_ = stack[2].m_num;
lean_object* v_toPure_2142_ = stack[3].m_obj;
lean_object* v_inst_2143_ = stack[4].m_obj;
lean_object* v_inst_2144_ = stack[5].m_obj;
lean_object* v_toBind_2145_ = stack[6].m_obj;
lean_object* v_getOpenDecls_2146_ = stack[7].m_obj;
lean_object* v_____do__lift_2147_ = stack[8].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2139_, v_id_2140_, v_allowEmpty_2141_, v_toPure_2142_, v_inst_2143_, v_inst_2144_, v_toBind_2145_, v_getOpenDecls_2146_, v_____do__lift_2147_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2152_, lean_object* v_id_2153_, lean_object* v_allowEmpty_2154_, lean_object* v_toPure_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_toBind_2158_, lean_object* v_getOpenDecls_2159_, lean_object* v_____do__lift_2160_){
_start:
{
uint8_t v_allowEmpty_boxed_2161_; lean_object* v_res_2162_; 
v_allowEmpty_boxed_2161_ = lean_unbox(v_allowEmpty_2154_);
v_res_2162_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2152_, v_id_2153_, v_allowEmpty_boxed_2161_, v_toPure_2155_, v_inst_2156_, v_inst_2157_, v_toBind_2158_, v_getOpenDecls_2159_, v_____do__lift_2160_);
return v_res_2162_;
}
}
lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2163_, lean_object* v_id_2164_, uint8_t v_allowEmpty_2165_, lean_object* v_toPure_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_toBind_2169_, lean_object* v_____do__lift_2170_){
_start:
{
lean_object* v_getCurrNamespace_2171_; lean_object* v_getOpenDecls_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; 
v_getCurrNamespace_2171_ = lean_ctor_get(v_inst_2163_, 0);
lean_inc(v_getCurrNamespace_2171_);
v_getOpenDecls_2172_ = lean_ctor_get(v_inst_2163_, 1);
lean_inc(v_getOpenDecls_2172_);
lean_dec_ref(v_inst_2163_);
v___x_2173_ = lean_box(v_allowEmpty_2165_);
lean_inc(v_toBind_2169_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2174_, 0, v_____do__lift_2170_);
lean_closure_set(v___f_2174_, 1, v_id_2164_);
lean_closure_set(v___f_2174_, 2, v___x_2173_);
lean_closure_set(v___f_2174_, 3, v_toPure_2166_);
lean_closure_set(v___f_2174_, 4, v_inst_2167_);
lean_closure_set(v___f_2174_, 5, v_inst_2168_);
lean_closure_set(v___f_2174_, 6, v_toBind_2169_);
lean_closure_set(v___f_2174_, 7, v_getOpenDecls_2172_);
v___x_2175_ = lean_apply_4(v_toBind_2169_, lean_box(0), lean_box(0), v_getCurrNamespace_2171_, v___f_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT void l_Lean_resolveNamespaceCore___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2163_ = stack[0].m_obj;
lean_object* v_id_2164_ = stack[1].m_obj;
uint8_t v_allowEmpty_2165_ = stack[2].m_num;
lean_object* v_toPure_2166_ = stack[3].m_obj;
lean_object* v_inst_2167_ = stack[4].m_obj;
lean_object* v_inst_2168_ = stack[5].m_obj;
lean_object* v_toBind_2169_ = stack[6].m_obj;
lean_object* v_____do__lift_2170_ = stack[7].m_obj;
lean_object* v_res_2176_;
v_res_2176_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2163_, v_id_2164_, v_allowEmpty_2165_, v_toPure_2166_, v_inst_2167_, v_inst_2168_, v_toBind_2169_, v_____do__lift_2170_);
stack->m_obj
 = v_res_2176_;
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2177_, lean_object* v_id_2178_, lean_object* v_allowEmpty_2179_, lean_object* v_toPure_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_toBind_2183_, lean_object* v_____do__lift_2184_){
_start:
{
uint8_t v_allowEmpty_boxed_2185_; lean_object* v_res_2186_; 
v_allowEmpty_boxed_2185_ = lean_unbox(v_allowEmpty_2179_);
v_res_2186_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2177_, v_id_2178_, v_allowEmpty_boxed_2185_, v_toPure_2180_, v_inst_2181_, v_inst_2182_, v_toBind_2183_, v_____do__lift_2184_);
return v_res_2186_;
}
}
lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_id_2191_, uint8_t v_allowEmpty_2192_){
_start:
{
lean_object* v_toApplicative_2193_; lean_object* v_toBind_2194_; lean_object* v_getEnv_2195_; lean_object* v_toPure_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_toApplicative_2193_ = lean_ctor_get(v_inst_2187_, 0);
v_toBind_2194_ = lean_ctor_get(v_inst_2187_, 1);
lean_inc_n(v_toBind_2194_, 2);
v_getEnv_2195_ = lean_ctor_get(v_inst_2189_, 0);
lean_inc(v_getEnv_2195_);
lean_dec_ref(v_inst_2189_);
v_toPure_2196_ = lean_ctor_get(v_toApplicative_2193_, 1);
lean_inc(v_toPure_2196_);
v___x_2197_ = lean_box(v_allowEmpty_2192_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2198_, 0, v_inst_2188_);
lean_closure_set(v___f_2198_, 1, v_id_2191_);
lean_closure_set(v___f_2198_, 2, v___x_2197_);
lean_closure_set(v___f_2198_, 3, v_toPure_2196_);
lean_closure_set(v___f_2198_, 4, v_inst_2187_);
lean_closure_set(v___f_2198_, 5, v_inst_2190_);
lean_closure_set(v___f_2198_, 6, v_toBind_2194_);
v___x_2199_ = lean_apply_4(v_toBind_2194_, lean_box(0), lean_box(0), v_getEnv_2195_, v___f_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT void l_Lean_resolveNamespaceCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2187_ = stack[0].m_obj;
lean_object* v_inst_2188_ = stack[1].m_obj;
lean_object* v_inst_2189_ = stack[2].m_obj;
lean_object* v_inst_2190_ = stack[3].m_obj;
lean_object* v_id_2191_ = stack[4].m_obj;
uint8_t v_allowEmpty_2192_ = stack[5].m_num;
lean_object* v_res_2200_;
v_res_2200_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2187_, v_inst_2188_, v_inst_2189_, v_inst_2190_, v_id_2191_, v_allowEmpty_2192_);
stack->m_obj
 = v_res_2200_;
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_id_2205_, lean_object* v_allowEmpty_2206_){
_start:
{
uint8_t v_allowEmpty_boxed_2207_; lean_object* v_res_2208_; 
v_allowEmpty_boxed_2207_ = lean_unbox(v_allowEmpty_2206_);
v_res_2208_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2201_, v_inst_2202_, v_inst_2203_, v_inst_2204_, v_id_2205_, v_allowEmpty_boxed_2207_);
return v_res_2208_;
}
}
lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_id_2214_, uint8_t v_allowEmpty_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2210_, v_inst_2211_, v_inst_2212_, v_inst_2213_, v_id_2214_, v_allowEmpty_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT void l_Lean_resolveNamespaceCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2210_ = stack[1].m_obj;
lean_object* v_inst_2211_ = stack[2].m_obj;
lean_object* v_inst_2212_ = stack[3].m_obj;
lean_object* v_inst_2213_ = stack[4].m_obj;
lean_object* v_id_2214_ = stack[5].m_obj;
uint8_t v_allowEmpty_2215_ = stack[6].m_num;
lean_object* v_res_2217_;
v_res_2217_ = l_Lean_resolveNamespaceCore(lean_box(0), v_inst_2210_, v_inst_2211_, v_inst_2212_, v_inst_2213_, v_id_2214_, v_allowEmpty_2215_);
stack->m_obj
 = v_res_2217_;
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_id_2223_, lean_object* v_allowEmpty_2224_){
_start:
{
uint8_t v_allowEmpty_boxed_2225_; lean_object* v_res_2226_; 
v_allowEmpty_boxed_2225_ = lean_unbox(v_allowEmpty_2224_);
v_res_2226_ = l_Lean_resolveNamespaceCore(v_m_2218_, v_inst_2219_, v_inst_2220_, v_inst_2221_, v_inst_2222_, v_id_2223_, v_allowEmpty_boxed_2225_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2227_){
_start:
{
if (lean_obj_tag(v_x_2227_) == 0)
{
lean_object* v_ns_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_ns_2228_ = lean_ctor_get(v_x_2227_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_x_2227_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v_x_2227_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_ns_2228_);
lean_dec(v_x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 1);
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_ns_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v___x_2236_; 
lean_dec_ref(v_x_2227_);
v___x_2236_ = lean_box(0);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2237_, lean_object* v_withRef_2238_, lean_object* v___x_2239_, lean_object* v_oldRef_2240_){
_start:
{
lean_object* v_ref_2241_; lean_object* v___x_2242_; 
v_ref_2241_ = l_Lean_replaceRef(v_x_2237_, v_oldRef_2240_);
v___x_2242_ = lean_apply_3(v_withRef_2238_, lean_box(0), v_ref_2241_, v___x_2239_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2243_, lean_object* v_withRef_2244_, lean_object* v___x_2245_, lean_object* v_oldRef_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2243_, v_withRef_2244_, v___x_2245_, v_oldRef_2246_);
lean_dec(v_oldRef_2246_);
lean_dec(v_x_2243_);
return v_res_2247_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2255_ = l_Lean_MessageData_ofFormat(v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_x_2260_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 3)
{
lean_object* v_toApplicative_2261_; lean_object* v_toBind_2262_; lean_object* v_toPure_2263_; lean_object* v_toMonadRef_2264_; lean_object* v_val_2265_; lean_object* v_preresolved_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v_pre_2269_; uint8_t v___x_2270_; 
v_toApplicative_2261_ = lean_ctor_get(v_inst_2256_, 0);
v_toBind_2262_ = lean_ctor_get(v_inst_2256_, 1);
lean_inc(v_toBind_2262_);
v_toPure_2263_ = lean_ctor_get(v_toApplicative_2261_, 1);
v_toMonadRef_2264_ = lean_ctor_get(v_inst_2259_, 1);
v_val_2265_ = lean_ctor_get(v_x_2260_, 2);
v_preresolved_2266_ = lean_ctor_get(v_x_2260_, 3);
v___f_2267_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2268_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2266_);
v_pre_2269_ = l_List_filterMapTR_go___redArg(v___f_2267_, v_preresolved_2266_, v___x_2268_);
v___x_2270_ = l_List_isEmpty___redArg(v_pre_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_inc(v_toPure_2263_);
lean_dec_ref_known(v_x_2260_, 4);
lean_dec(v_toBind_2262_);
lean_dec_ref(v_inst_2259_);
lean_dec_ref(v_inst_2258_);
lean_dec_ref(v_inst_2257_);
lean_dec_ref(v_inst_2256_);
v___x_2271_ = lean_apply_2(v_toPure_2263_, lean_box(0), v_pre_2269_);
return v___x_2271_;
}
else
{
lean_object* v_getRef_2272_; lean_object* v_withRef_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; 
lean_dec(v_pre_2269_);
v_getRef_2272_ = lean_ctor_get(v_toMonadRef_2264_, 0);
lean_inc(v_getRef_2272_);
v_withRef_2273_ = lean_ctor_get(v_toMonadRef_2264_, 1);
lean_inc(v_withRef_2273_);
v___x_2274_ = 0;
lean_inc(v_val_2265_);
v___x_2275_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2256_, v_inst_2257_, v_inst_2258_, v_inst_2259_, v_val_2265_, v___x_2274_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2276_, 0, v_x_2260_);
lean_closure_set(v___f_2276_, 1, v_withRef_2273_);
lean_closure_set(v___f_2276_, 2, v___x_2275_);
v___x_2277_ = lean_apply_4(v_toBind_2262_, lean_box(0), lean_box(0), v_getRef_2272_, v___f_2276_);
return v___x_2277_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_inst_2258_);
lean_dec_ref(v_inst_2257_);
v___x_2278_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2279_ = l_Lean_throwErrorAt___redArg(v_inst_2256_, v_inst_2259_, v_x_2260_, v___x_2278_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_resolveNamespace___redArg(v_inst_2281_, v_inst_2282_, v_inst_2283_, v_inst_2284_, v_x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2289_, lean_object* v___f_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_toPure_2293_, lean_object* v_____do__lift_2294_){
_start:
{
if (lean_obj_tag(v_____do__lift_2294_) == 1)
{
lean_object* v_tail_2310_; 
v_tail_2310_ = lean_ctor_get(v_____do__lift_2294_, 1);
if (lean_obj_tag(v_tail_2310_) == 0)
{
lean_object* v_head_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_inst_2291_);
lean_dec_ref(v___f_2290_);
v_head_2311_ = lean_ctor_get(v_____do__lift_2294_, 0);
lean_inc(v_head_2311_);
lean_dec_ref_known(v_____do__lift_2294_, 2);
v___x_2312_ = lean_apply_2(v_toPure_2293_, lean_box(0), v_head_2311_);
return v___x_2312_;
}
else
{
lean_dec(v_toPure_2293_);
goto v___jp_2295_;
}
}
else
{
lean_dec(v_toPure_2293_);
goto v___jp_2295_;
}
v___jp_2295_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2296_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2297_ = l_Lean_TSyntax_getId(v_id_2289_);
v___x_2298_ = 1;
v___x_2299_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2297_, v___x_2298_);
v___x_2300_ = lean_string_append(v___x_2296_, v___x_2299_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2302_ = lean_string_append(v___x_2300_, v___x_2301_);
v___x_2303_ = l_List_toString___redArg(v___f_2290_, v_____do__lift_2294_);
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
v___x_2309_ = l_Lean_throwError___redArg(v_inst_2291_, v_inst_2292_, v___x_2308_);
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2313_, lean_object* v___f_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_toPure_2317_, lean_object* v_____do__lift_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2313_, v___f_2314_, v_inst_2315_, v_inst_2316_, v_toPure_2317_, v_____do__lift_2318_);
lean_dec(v_id_2313_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_id_2325_){
_start:
{
lean_object* v_toApplicative_2326_; lean_object* v_toBind_2327_; lean_object* v_toPure_2328_; lean_object* v___f_2329_; lean_object* v___x_2330_; lean_object* v___f_2331_; lean_object* v___x_2332_; 
v_toApplicative_2326_ = lean_ctor_get(v_inst_2321_, 0);
v_toBind_2327_ = lean_ctor_get(v_inst_2321_, 1);
lean_inc(v_toBind_2327_);
v_toPure_2328_ = lean_ctor_get(v_toApplicative_2326_, 1);
lean_inc(v_toPure_2328_);
v___f_2329_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2325_);
lean_inc_ref(v_inst_2324_);
lean_inc_ref(v_inst_2321_);
v___x_2330_ = l_Lean_resolveNamespace___redArg(v_inst_2321_, v_inst_2322_, v_inst_2323_, v_inst_2324_, v_id_2325_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2331_, 0, v_id_2325_);
lean_closure_set(v___f_2331_, 1, v___f_2329_);
lean_closure_set(v___f_2331_, 2, v_inst_2321_);
lean_closure_set(v___f_2331_, 3, v_inst_2324_);
lean_closure_set(v___f_2331_, 4, v_toPure_2328_);
v___x_2332_ = lean_apply_4(v_toBind_2327_, lean_box(0), lean_box(0), v___x_2330_, v___f_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_id_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2334_, v_inst_2335_, v_inst_2336_, v_inst_2337_, v_id_2338_);
return v___x_2339_;
}
}
uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2340_){
_start:
{
lean_object* v_snd_2341_; uint8_t v___x_2342_; 
v_snd_2341_ = lean_ctor_get(v_x_2340_, 1);
v___x_2342_ = l_List_isEmpty___redArg(v_snd_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT void l_Lean_filterFieldList___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2340_ = stack[0].m_obj;
uint8_t v_res_2343_;
v_res_2343_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2340_);
stack->m_num = v_res_2343_;
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2344_){
_start:
{
uint8_t v_res_2345_; lean_object* v_r_2346_; 
v_res_2345_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2344_);
lean_dec_ref(v_x_2344_);
v_r_2346_ = lean_box(v_res_2345_);
return v_r_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2347_){
_start:
{
lean_object* v_fst_2348_; 
v_fst_2348_ = lean_ctor_get(v_x_2347_, 0);
lean_inc(v_fst_2348_);
return v_fst_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2349_);
lean_dec_ref(v_x_2349_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2351_, lean_object* v_cs_2352_, lean_object* v_toPure_2353_, lean_object* v_____r_2354_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_box(0);
v___x_2356_ = l_List_mapTR_loop___redArg(v___f_2351_, v_cs_2352_, v___x_2355_);
v___x_2357_ = lean_apply_2(v_toPure_2353_, lean_box(0), v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2358_, lean_object* v_____r_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_apply_1(v___f_2358_, v_____r_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_n_2364_, lean_object* v_toBind_2365_, lean_object* v___f_2366_, lean_object* v_____do__lift_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2361_, v_inst_2362_, v_inst_2363_, v_____do__lift_2367_, v_n_2364_);
v___x_2369_ = lean_apply_4(v_toBind_2365_, lean_box(0), lean_box(0), v___x_2368_, v___f_2366_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_, lean_object* v_n_2375_, lean_object* v_cs_2376_){
_start:
{
lean_object* v_toApplicative_2377_; lean_object* v_toBind_2378_; lean_object* v_toPure_2379_; lean_object* v_toMonadRef_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v_cs_2384_; lean_object* v___f_2385_; uint8_t v___x_2386_; 
v_toApplicative_2377_ = lean_ctor_get(v_inst_2372_, 0);
v_toBind_2378_ = lean_ctor_get(v_inst_2372_, 1);
lean_inc(v_toBind_2378_);
v_toPure_2379_ = lean_ctor_get(v_toApplicative_2377_, 1);
v_toMonadRef_2380_ = lean_ctor_get(v_inst_2374_, 1);
v___f_2381_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2382_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2383_ = lean_box(0);
v_cs_2384_ = l_List_filterTR_loop___redArg(v___f_2381_, v_cs_2376_, v___x_2383_);
lean_inc(v_toPure_2379_);
lean_inc(v_cs_2384_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2385_, 0, v___f_2382_);
lean_closure_set(v___f_2385_, 1, v_cs_2384_);
lean_closure_set(v___f_2385_, 2, v_toPure_2379_);
v___x_2386_ = l_List_isEmpty___redArg(v_cs_2384_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_inc(v_toPure_2379_);
lean_dec_ref(v___f_2385_);
lean_dec(v_toBind_2378_);
lean_dec(v_n_2375_);
lean_dec_ref(v_inst_2374_);
lean_dec_ref(v_inst_2373_);
lean_dec_ref(v_inst_2372_);
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2382_, v_cs_2384_, v_toPure_2379_, v___x_2387_);
return v___x_2388_;
}
else
{
lean_object* v_getRef_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; 
lean_dec(v_cs_2384_);
v_getRef_2389_ = lean_ctor_get(v_toMonadRef_2380_, 0);
lean_inc(v_getRef_2389_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2390_, 0, v___f_2385_);
lean_inc(v_toBind_2378_);
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2391_, 0, v_inst_2372_);
lean_closure_set(v___f_2391_, 1, v_inst_2373_);
lean_closure_set(v___f_2391_, 2, v_inst_2374_);
lean_closure_set(v___f_2391_, 3, v_n_2375_);
lean_closure_set(v___f_2391_, 4, v_toBind_2378_);
lean_closure_set(v___f_2391_, 5, v___f_2390_);
v___x_2392_ = lean_apply_4(v_toBind_2378_, lean_box(0), lean_box(0), v_getRef_2389_, v___f_2391_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2393_, lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_n_2397_, lean_object* v_cs_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_filterFieldList___redArg(v_inst_2394_, v_inst_2395_, v_inst_2396_, v_n_2397_, v_cs_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_n_2403_, lean_object* v_cs_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_filterFieldList___redArg(v_inst_2400_, v_inst_2401_, v_inst_2402_, v_n_2403_, v_cs_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_n_2413_){
_start:
{
lean_object* v_toBind_2414_; lean_object* v___f_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_toBind_2414_ = lean_ctor_get(v_inst_2406_, 1);
lean_inc(v_toBind_2414_);
lean_inc(v_n_2413_);
lean_inc_ref(v_inst_2408_);
lean_inc_ref(v_inst_2406_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2415_, 0, v_inst_2406_);
lean_closure_set(v___f_2415_, 1, v_inst_2408_);
lean_closure_set(v___f_2415_, 2, v_inst_2412_);
lean_closure_set(v___f_2415_, 3, v_n_2413_);
v___x_2416_ = 1;
v___x_2417_ = l_Lean_resolveGlobalName___redArg(v_inst_2406_, v_inst_2407_, v_inst_2408_, v_inst_2409_, v_inst_2410_, v_inst_2411_, v_n_2413_, v___x_2416_);
v___x_2418_ = lean_apply_4(v_toBind_2414_, lean_box(0), lean_box(0), v___x_2417_, v___f_2415_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_n_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2420_, v_inst_2421_, v_inst_2422_, v_inst_2423_, v_inst_2424_, v_inst_2425_, v_inst_2426_, v_n_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2429_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_box(0);
v___x_2431_ = l_Lean_mkConst(v_declName_2429_, v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_n_2442_, lean_object* v_cs_2443_){
_start:
{
lean_object* v_toApplicative_2444_; lean_object* v_toPure_2445_; lean_object* v___f_2446_; 
v_toApplicative_2444_ = lean_ctor_get(v_inst_2440_, 0);
v_toPure_2445_ = lean_ctor_get(v_toApplicative_2444_, 1);
v___f_2446_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2443_) == 1)
{
lean_object* v_tail_2460_; 
v_tail_2460_ = lean_ctor_get(v_cs_2443_, 1);
if (lean_obj_tag(v_tail_2460_) == 0)
{
lean_object* v_head_2461_; lean_object* v___x_2462_; 
lean_inc(v_toPure_2445_);
lean_dec(v_n_2442_);
lean_dec_ref(v_inst_2441_);
lean_dec_ref(v_inst_2440_);
v_head_2461_ = lean_ctor_get(v_cs_2443_, 0);
lean_inc(v_head_2461_);
lean_dec_ref_known(v_cs_2443_, 2);
v___x_2462_ = lean_apply_2(v_toPure_2445_, lean_box(0), v_head_2461_);
return v___x_2462_;
}
else
{
goto v___jp_2447_;
}
}
else
{
goto v___jp_2447_;
}
v___jp_2447_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2448_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2449_ = l_Lean_MessageData_ofName(v_n_2442_);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_box(0);
v___x_2454_ = l_List_mapTR_loop___redArg(v___f_2446_, v_cs_2443_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2456_ = l_List_mapTR_loop___redArg(v___x_2455_, v___x_2454_, v___x_2453_);
v___x_2457_ = l_Lean_MessageData_ofList(v___x_2456_);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2452_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_throwError___redArg(v_inst_2440_, v_inst_2441_, v___x_2458_);
return v___x_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_n_2466_, lean_object* v_cs_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_ensureNoOverload___redArg(v_inst_2464_, v_inst_2465_, v_n_2466_, v_cs_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2469_, lean_object* v_inst_2470_, lean_object* v_n_2471_, lean_object* v_____do__lift_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_ensureNoOverload___redArg(v_inst_2469_, v_inst_2470_, v_n_2471_, v_____do__lift_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_n_2481_){
_start:
{
lean_object* v_toBind_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_toBind_2482_ = lean_ctor_get(v_inst_2474_, 1);
lean_inc(v_toBind_2482_);
lean_inc(v_n_2481_);
lean_inc_ref(v_inst_2480_);
lean_inc_ref(v_inst_2474_);
v___f_2483_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2483_, 0, v_inst_2474_);
lean_closure_set(v___f_2483_, 1, v_inst_2480_);
lean_closure_set(v___f_2483_, 2, v_n_2481_);
v___x_2484_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2474_, v_inst_2475_, v_inst_2476_, v_inst_2477_, v_inst_2478_, v_inst_2479_, v_inst_2480_, v_n_2481_);
v___x_2485_ = lean_apply_4(v_toBind_2482_, lean_box(0), lean_box(0), v___x_2484_, v___f_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_n_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2487_, v_inst_2488_, v_inst_2489_, v_inst_2490_, v_inst_2491_, v_inst_2492_, v_inst_2493_, v_n_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2496_){
_start:
{
if (lean_obj_tag(v_x_2496_) == 1)
{
lean_object* v_fields_2497_; 
v_fields_2497_ = lean_ctor_get(v_x_2496_, 1);
if (lean_obj_tag(v_fields_2497_) == 0)
{
lean_object* v_n_2498_; lean_object* v___x_2499_; 
v_n_2498_ = lean_ctor_get(v_x_2496_, 0);
lean_inc(v_n_2498_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_n_2498_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_box(0);
return v___x_2500_;
}
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_box(0);
return v___x_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2502_);
lean_dec_ref(v_x_2502_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2504_, lean_object* v_withRef_2505_, lean_object* v___x_2506_, lean_object* v_oldRef_2507_){
_start:
{
lean_object* v_ref_2508_; lean_object* v___x_2509_; 
v_ref_2508_ = l_Lean_replaceRef(v_stx_2504_, v_oldRef_2507_);
v___x_2509_ = lean_apply_3(v_withRef_2505_, lean_box(0), v_ref_2508_, v___x_2506_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2510_, lean_object* v_withRef_2511_, lean_object* v___x_2512_, lean_object* v_oldRef_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2510_, v_withRef_2511_, v___x_2512_, v_oldRef_2513_);
lean_dec(v_oldRef_2513_);
lean_dec(v_stx_2510_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_stx_2518_, lean_object* v_k_2519_){
_start:
{
if (lean_obj_tag(v_stx_2518_) == 3)
{
lean_object* v_toApplicative_2520_; lean_object* v_toBind_2521_; lean_object* v_toPure_2522_; lean_object* v_toMonadRef_2523_; lean_object* v_val_2524_; lean_object* v_preresolved_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v_pre_2528_; uint8_t v___x_2529_; 
v_toApplicative_2520_ = lean_ctor_get(v_inst_2516_, 0);
lean_inc_ref(v_toApplicative_2520_);
v_toBind_2521_ = lean_ctor_get(v_inst_2516_, 1);
lean_inc(v_toBind_2521_);
lean_dec_ref(v_inst_2516_);
v_toPure_2522_ = lean_ctor_get(v_toApplicative_2520_, 1);
lean_inc(v_toPure_2522_);
lean_dec_ref(v_toApplicative_2520_);
v_toMonadRef_2523_ = lean_ctor_get(v_inst_2517_, 1);
lean_inc_ref(v_toMonadRef_2523_);
lean_dec_ref(v_inst_2517_);
v_val_2524_ = lean_ctor_get(v_stx_2518_, 2);
v_preresolved_2525_ = lean_ctor_get(v_stx_2518_, 3);
v___f_2526_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2527_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2525_);
v_pre_2528_ = l_List_filterMapTR_go___redArg(v___f_2526_, v_preresolved_2525_, v___x_2527_);
v___x_2529_ = l_List_isEmpty___redArg(v_pre_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref(v_toMonadRef_2523_);
lean_dec(v_toBind_2521_);
lean_dec_ref_known(v_stx_2518_, 4);
lean_dec(v_k_2519_);
v___x_2530_ = lean_apply_2(v_toPure_2522_, lean_box(0), v_pre_2528_);
return v___x_2530_;
}
else
{
lean_object* v_getRef_2531_; lean_object* v_withRef_2532_; lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; 
lean_dec(v_pre_2528_);
lean_dec(v_toPure_2522_);
v_getRef_2531_ = lean_ctor_get(v_toMonadRef_2523_, 0);
lean_inc(v_getRef_2531_);
v_withRef_2532_ = lean_ctor_get(v_toMonadRef_2523_, 1);
lean_inc(v_withRef_2532_);
lean_dec_ref(v_toMonadRef_2523_);
lean_inc(v_val_2524_);
v___x_2533_ = lean_apply_1(v_k_2519_, v_val_2524_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2534_, 0, v_stx_2518_);
lean_closure_set(v___f_2534_, 1, v_withRef_2532_);
lean_closure_set(v___f_2534_, 2, v___x_2533_);
v___x_2535_ = lean_apply_4(v_toBind_2521_, lean_box(0), lean_box(0), v_getRef_2531_, v___f_2534_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v_k_2519_);
v___x_2536_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2537_ = l_Lean_throwErrorAt___redArg(v_inst_2516_, v_inst_2517_, v_stx_2518_, v___x_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2538_, lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_stx_2541_, lean_object* v_k_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2539_, v_inst_2540_, v_stx_2541_, v_k_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_stx_2551_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_inc_ref(v_inst_2550_);
lean_inc_ref(v_inst_2544_);
v___x_2552_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2552_, 0, lean_box(0));
lean_closure_set(v___x_2552_, 1, v_inst_2544_);
lean_closure_set(v___x_2552_, 2, v_inst_2545_);
lean_closure_set(v___x_2552_, 3, v_inst_2546_);
lean_closure_set(v___x_2552_, 4, v_inst_2547_);
lean_closure_set(v___x_2552_, 5, v_inst_2548_);
lean_closure_set(v___x_2552_, 6, v_inst_2549_);
lean_closure_set(v___x_2552_, 7, v_inst_2550_);
v___x_2553_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2544_, v_inst_2550_, v_stx_2551_, v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_stx_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_resolveGlobalConst___redArg(v_inst_2555_, v_inst_2556_, v_inst_2557_, v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_stx_2562_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2565_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2566_ = lean_unsigned_to_nat(11u);
v___x_2567_ = lean_unsigned_to_nat(429u);
v___x_2568_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2569_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2570_ = l_mkPanicMessageWithDecl(v___x_2569_, v___x_2568_, v___x_2567_, v___x_2566_, v___x_2565_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_id_2576_, lean_object* v_cs_2577_){
_start:
{
if (lean_obj_tag(v_cs_2577_) == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v_id_2576_);
lean_dec_ref(v_inst_2575_);
v___x_2578_ = lean_box(0);
v___x_2579_ = l_instInhabitedOfMonad___redArg(v_inst_2574_, v___x_2578_);
v___x_2580_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2581_ = l_panic___redArg(v___x_2579_, v___x_2580_);
lean_dec(v___x_2579_);
return v___x_2581_;
}
else
{
lean_object* v_tail_2582_; 
v_tail_2582_ = lean_ctor_get(v_cs_2577_, 1);
if (lean_obj_tag(v_tail_2582_) == 0)
{
lean_object* v_toApplicative_2583_; lean_object* v_toPure_2584_; lean_object* v_head_2585_; lean_object* v___x_2586_; 
v_toApplicative_2583_ = lean_ctor_get(v_inst_2574_, 0);
lean_inc_ref(v_toApplicative_2583_);
lean_dec(v_id_2576_);
lean_dec_ref(v_inst_2575_);
lean_dec_ref(v_inst_2574_);
v_toPure_2584_ = lean_ctor_get(v_toApplicative_2583_, 1);
lean_inc(v_toPure_2584_);
lean_dec_ref(v_toApplicative_2583_);
v_head_2585_ = lean_ctor_get(v_cs_2577_, 0);
lean_inc(v_head_2585_);
lean_dec_ref_known(v_cs_2577_, 2);
v___x_2586_ = lean_apply_2(v_toPure_2584_, lean_box(0), v_head_2585_);
return v___x_2586_;
}
else
{
lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___f_2587_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2588_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2589_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2590_ = lean_box(0);
v___x_2591_ = 0;
lean_inc(v_id_2576_);
v___x_2592_ = l_Lean_Syntax_formatStx(v_id_2576_, v___x_2590_, v___x_2591_);
v___x_2593_ = l_Std_Format_defWidth;
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = l_Std_Format_pretty(v___x_2592_, v___x_2593_, v___x_2594_, v___x_2594_);
v___x_2596_ = lean_string_append(v___x_2589_, v___x_2595_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2598_ = lean_string_append(v___x_2596_, v___x_2597_);
v___x_2599_ = lean_box(0);
v___x_2600_ = l_List_mapTR_loop___redArg(v___f_2587_, v_cs_2577_, v___x_2599_);
v___x_2601_ = l_List_toString___redArg(v___x_2588_, v___x_2600_);
v___x_2602_ = lean_string_append(v___x_2598_, v___x_2601_);
lean_dec_ref(v___x_2601_);
v___x_2603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___x_2604_ = l_Lean_MessageData_ofFormat(v___x_2603_);
v___x_2605_ = l_Lean_throwErrorAt___redArg(v_inst_2574_, v_inst_2575_, v_id_2576_, v___x_2604_);
return v___x_2605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_id_2609_, lean_object* v_cs_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2607_, v_inst_2608_, v_id_2609_, v_cs_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_id_2614_, lean_object* v_____do__lift_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2612_, v_inst_2613_, v_id_2614_, v_____do__lift_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_id_2624_){
_start:
{
lean_object* v_toBind_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_toBind_2625_ = lean_ctor_get(v_inst_2617_, 1);
lean_inc(v_toBind_2625_);
lean_inc(v_id_2624_);
lean_inc_ref(v_inst_2623_);
lean_inc_ref(v_inst_2617_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2626_, 0, v_inst_2617_);
lean_closure_set(v___f_2626_, 1, v_inst_2623_);
lean_closure_set(v___f_2626_, 2, v_id_2624_);
v___x_2627_ = l_Lean_resolveGlobalConst___redArg(v_inst_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_inst_2623_, v_id_2624_);
v___x_2628_ = lean_apply_4(v_toBind_2625_, lean_box(0), lean_box(0), v___x_2627_, v___f_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_id_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2630_, v_inst_2631_, v_inst_2632_, v_inst_2633_, v_inst_2634_, v_inst_2635_, v_inst_2636_, v_id_2637_);
return v___x_2638_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2639_, lean_object* v___f_2640_, uint8_t v_globalDeclFoundNext_2641_, uint8_t v_globalDeclFound_2642_, lean_object* v_r_2643_){
_start:
{
lean_object* v___x_2644_; lean_object* v_r_2645_; uint8_t v___x_2646_; 
v___x_2644_ = lean_box(0);
v_r_2645_ = l_List_filterTR_loop___redArg(v___f_2639_, v_r_2643_, v___x_2644_);
v___x_2646_ = l_List_isEmpty___redArg(v_r_2645_);
lean_dec(v_r_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_box(v_globalDeclFoundNext_2641_);
v___x_2649_ = lean_apply_2(v___f_2640_, v___x_2647_, v___x_2648_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_box(0);
v___x_2651_ = lean_box(v_globalDeclFound_2642_);
v___x_2652_ = lean_apply_2(v___f_2640_, v___x_2650_, v___x_2651_);
return v___x_2652_;
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2639_ = stack[0].m_obj;
lean_object* v___f_2640_ = stack[1].m_obj;
uint8_t v_globalDeclFoundNext_2641_ = stack[2].m_num;
uint8_t v_globalDeclFound_2642_ = stack[3].m_num;
lean_object* v_r_2643_ = stack[4].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2639_, v___f_2640_, v_globalDeclFoundNext_2641_, v_globalDeclFound_2642_, v_r_2643_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2654_, lean_object* v___f_2655_, lean_object* v_globalDeclFoundNext_2656_, lean_object* v_globalDeclFound_2657_, lean_object* v_r_2658_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2659_; uint8_t v_globalDeclFound_boxed_2660_; lean_object* v_res_2661_; 
v_globalDeclFoundNext_boxed_2659_ = lean_unbox(v_globalDeclFoundNext_2656_);
v_globalDeclFound_boxed_2660_ = lean_unbox(v_globalDeclFound_2657_);
v_res_2661_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2654_, v___f_2655_, v_globalDeclFoundNext_boxed_2659_, v_globalDeclFound_boxed_2660_, v_r_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2662_, lean_object* v_projs_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_view_2670_, lean_object* v_findLocalDecl_x3f_2671_, lean_object* v_pre_2672_, lean_object* v_____r_2673_, lean_object* v_globalDeclFoundNext_2674_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2675_; lean_object* v_res_2676_; 
v_globalDeclFoundNext_boxed_2675_ = lean_unbox(v_globalDeclFoundNext_2674_);
v_res_2676_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2662_, v_projs_2663_, v_inst_2664_, v_inst_2665_, v_inst_2666_, v_inst_2667_, v_inst_2668_, v_inst_2669_, v_view_2670_, v_findLocalDecl_x3f_2671_, v_pre_2672_, v_____r_2673_, v_globalDeclFoundNext_boxed_2675_);
return v_res_2676_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_view_2683_, lean_object* v_findLocalDecl_x3f_2684_, lean_object* v_n_2685_, lean_object* v_projs_2686_, uint8_t v_globalDeclFound_2687_){
_start:
{
lean_object* v_toApplicative_2688_; lean_object* v_imported_2689_; lean_object* v_ctx_2690_; lean_object* v_scopes_2691_; lean_object* v_toBind_2692_; lean_object* v_toPure_2693_; lean_object* v___f_2694_; lean_object* v_givenNameView_2695_; uint8_t v___y_2697_; 
v_toApplicative_2688_ = lean_ctor_get(v_inst_2677_, 0);
v_imported_2689_ = lean_ctor_get(v_view_2683_, 1);
v_ctx_2690_ = lean_ctor_get(v_view_2683_, 2);
v_scopes_2691_ = lean_ctor_get(v_view_2683_, 3);
v_toBind_2692_ = lean_ctor_get(v_inst_2677_, 1);
v_toPure_2693_ = lean_ctor_get(v_toApplicative_2688_, 1);
v___f_2694_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2691_);
lean_inc(v_ctx_2690_);
lean_inc(v_imported_2689_);
lean_inc(v_n_2685_);
v_givenNameView_2695_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2695_, 0, v_n_2685_);
lean_ctor_set(v_givenNameView_2695_, 1, v_imported_2689_);
lean_ctor_set(v_givenNameView_2695_, 2, v_ctx_2690_);
lean_ctor_set(v_givenNameView_2695_, 3, v_scopes_2691_);
if (v_globalDeclFound_2687_ == 0)
{
v___y_2697_ = v_globalDeclFound_2687_;
goto v___jp_2696_;
}
else
{
uint8_t v___x_2733_; 
v___x_2733_ = l_List_isEmpty___redArg(v_projs_2686_);
if (v___x_2733_ == 0)
{
v___y_2697_ = v_globalDeclFound_2687_;
goto v___jp_2696_;
}
else
{
uint8_t v___x_2734_; 
v___x_2734_ = 0;
v___y_2697_ = v___x_2734_;
goto v___jp_2696_;
}
}
v___jp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_box(v___y_2697_);
lean_inc_ref(v_findLocalDecl_x3f_2684_);
lean_inc_ref(v_givenNameView_2695_);
v___x_2699_ = lean_apply_2(v_findLocalDecl_x3f_2684_, v_givenNameView_2695_, v___x_2698_);
if (lean_obj_tag(v___x_2699_) == 0)
{
if (lean_obj_tag(v_n_2685_) == 1)
{
lean_object* v_pre_2700_; lean_object* v_str_2701_; lean_object* v___f_2702_; 
v_pre_2700_ = lean_ctor_get(v_n_2685_, 0);
lean_inc_n(v_pre_2700_, 2);
v_str_2701_ = lean_ctor_get(v_n_2685_, 1);
lean_inc_ref_n(v_str_2701_, 2);
lean_dec_ref_known(v_n_2685_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2684_);
lean_inc_ref(v_view_2683_);
lean_inc(v_inst_2682_);
lean_inc_ref(v_inst_2681_);
lean_inc_ref(v_inst_2680_);
lean_inc_ref(v_inst_2679_);
lean_inc_ref(v_inst_2678_);
lean_inc_ref(v_inst_2677_);
lean_inc(v_projs_2686_);
v___f_2702_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2702_, 0, v_str_2701_);
lean_closure_set(v___f_2702_, 1, v_projs_2686_);
lean_closure_set(v___f_2702_, 2, v_inst_2677_);
lean_closure_set(v___f_2702_, 3, v_inst_2678_);
lean_closure_set(v___f_2702_, 4, v_inst_2679_);
lean_closure_set(v___f_2702_, 5, v_inst_2680_);
lean_closure_set(v___f_2702_, 6, v_inst_2681_);
lean_closure_set(v___f_2702_, 7, v_inst_2682_);
lean_closure_set(v___f_2702_, 8, v_view_2683_);
lean_closure_set(v___f_2702_, 9, v_findLocalDecl_x3f_2684_);
lean_closure_set(v___f_2702_, 10, v_pre_2700_);
if (v_globalDeclFound_2687_ == 0)
{
uint8_t v_globalDeclFoundNext_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc(v_toBind_2692_);
lean_dec_ref(v_str_2701_);
lean_dec(v_pre_2700_);
lean_dec(v_projs_2686_);
lean_dec_ref(v_findLocalDecl_x3f_2684_);
lean_dec_ref(v_view_2683_);
v_globalDeclFoundNext_2703_ = 1;
v___x_2704_ = lean_box(v_globalDeclFoundNext_2703_);
v___x_2705_ = lean_box(v_globalDeclFound_2687_);
v___f_2706_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2706_, 0, v___f_2694_);
lean_closure_set(v___f_2706_, 1, v___f_2702_);
lean_closure_set(v___f_2706_, 2, v___x_2704_);
lean_closure_set(v___f_2706_, 3, v___x_2705_);
v___x_2707_ = l_Lean_MacroScopesView_review(v_givenNameView_2695_);
v___x_2708_ = l_Lean_resolveGlobalName___redArg(v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v___x_2707_, v_globalDeclFound_2687_);
v___x_2709_ = lean_apply_4(v_toBind_2692_, lean_box(0), lean_box(0), v___x_2708_, v___f_2706_);
return v___x_2709_;
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v___f_2702_);
lean_dec_ref_known(v_givenNameView_2695_, 4);
v___x_2710_ = lean_box(0);
v___x_2711_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2701_, v_projs_2686_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_view_2683_, v_findLocalDecl_x3f_2684_, v_pre_2700_, v___x_2710_, v_globalDeclFound_2687_);
return v___x_2711_;
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_inc(v_toPure_2693_);
lean_dec_ref_known(v_givenNameView_2695_, 4);
lean_dec(v_projs_2686_);
lean_dec(v_n_2685_);
lean_dec_ref(v_findLocalDecl_x3f_2684_);
lean_dec_ref(v_view_2683_);
lean_dec(v_inst_2682_);
lean_dec_ref(v_inst_2681_);
lean_dec_ref(v_inst_2680_);
lean_dec_ref(v_inst_2679_);
lean_dec_ref(v_inst_2678_);
lean_dec_ref(v_inst_2677_);
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_apply_2(v_toPure_2693_, lean_box(0), v___x_2712_);
return v___x_2713_;
}
}
else
{
lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2730_; 
lean_inc(v_toPure_2693_);
lean_dec_ref_known(v_givenNameView_2695_, 4);
lean_dec(v_n_2685_);
lean_dec_ref(v_findLocalDecl_x3f_2684_);
lean_dec_ref(v_view_2683_);
lean_dec(v_inst_2682_);
lean_dec_ref(v_inst_2681_);
lean_dec_ref(v_inst_2680_);
lean_dec_ref(v_inst_2679_);
lean_dec_ref(v_inst_2678_);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_inst_2677_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2731_ = lean_ctor_get(v_inst_2677_, 1);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_inst_2677_, 0);
lean_dec(v_unused_2732_);
v___x_2715_ = v_inst_2677_;
v_isShared_2716_ = v_isSharedCheck_2730_;
goto v_resetjp_2714_;
}
else
{
lean_dec(v_inst_2677_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2730_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_val_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2729_; 
v_val_2717_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2719_ = v___x_2699_;
v_isShared_2720_ = v_isSharedCheck_2729_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_val_2717_);
lean_dec(v___x_2699_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2729_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = l_Lean_LocalDecl_toExpr(v_val_2717_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v_projs_2686_);
lean_ctor_set(v___x_2715_, 0, v___x_2721_);
v___x_2723_ = v___x_2715_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_projs_2686_);
v___x_2723_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2725_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2723_);
v___x_2725_ = v___x_2719_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_apply_2(v_toPure_2693_, lean_box(0), v___x_2725_);
return v___x_2726_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2677_ = stack[0].m_obj;
lean_object* v_inst_2678_ = stack[1].m_obj;
lean_object* v_inst_2679_ = stack[2].m_obj;
lean_object* v_inst_2680_ = stack[3].m_obj;
lean_object* v_inst_2681_ = stack[4].m_obj;
lean_object* v_inst_2682_ = stack[5].m_obj;
lean_object* v_view_2683_ = stack[6].m_obj;
lean_object* v_findLocalDecl_x3f_2684_ = stack[7].m_obj;
lean_object* v_n_2685_ = stack[8].m_obj;
lean_object* v_projs_2686_ = stack[9].m_obj;
uint8_t v_globalDeclFound_2687_ = stack[10].m_num;
lean_object* v_res_2735_;
v_res_2735_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_view_2683_, v_findLocalDecl_x3f_2684_, v_n_2685_, v_projs_2686_, v_globalDeclFound_2687_);
stack->m_obj
 = v_res_2735_;
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2736_, lean_object* v_projs_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_view_2744_, lean_object* v_findLocalDecl_x3f_2745_, lean_object* v_pre_2746_, lean_object* v_____r_2747_, uint8_t v_globalDeclFoundNext_2748_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_str_2736_);
lean_ctor_set(v___x_2749_, 1, v_projs_2737_);
v___x_2750_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_view_2744_, v_findLocalDecl_x3f_2745_, v_pre_2746_, v___x_2749_, v_globalDeclFoundNext_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_str_2736_ = stack[0].m_obj;
lean_object* v_projs_2737_ = stack[1].m_obj;
lean_object* v_inst_2738_ = stack[2].m_obj;
lean_object* v_inst_2739_ = stack[3].m_obj;
lean_object* v_inst_2740_ = stack[4].m_obj;
lean_object* v_inst_2741_ = stack[5].m_obj;
lean_object* v_inst_2742_ = stack[6].m_obj;
lean_object* v_inst_2743_ = stack[7].m_obj;
lean_object* v_view_2744_ = stack[8].m_obj;
lean_object* v_findLocalDecl_x3f_2745_ = stack[9].m_obj;
lean_object* v_pre_2746_ = stack[10].m_obj;
lean_object* v_____r_2747_ = stack[11].m_obj;
uint8_t v_globalDeclFoundNext_2748_ = stack[12].m_num;
lean_object* v_res_2751_;
v_res_2751_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2736_, v_projs_2737_, v_inst_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_view_2744_, v_findLocalDecl_x3f_2745_, v_pre_2746_, v_____r_2747_, v_globalDeclFoundNext_2748_);
stack->m_obj
 = v_res_2751_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_view_2758_, lean_object* v_findLocalDecl_x3f_2759_, lean_object* v_n_2760_, lean_object* v_projs_2761_, lean_object* v_globalDeclFound_2762_){
_start:
{
uint8_t v_globalDeclFound_boxed_2763_; lean_object* v_res_2764_; 
v_globalDeclFound_boxed_2763_ = lean_unbox(v_globalDeclFound_2762_);
v_res_2764_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2752_, v_inst_2753_, v_inst_2754_, v_inst_2755_, v_inst_2756_, v_inst_2757_, v_view_2758_, v_findLocalDecl_x3f_2759_, v_n_2760_, v_projs_2761_, v_globalDeclFound_boxed_2763_);
return v_res_2764_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_inst_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v_view_2772_, lean_object* v_findLocalDecl_x3f_2773_, lean_object* v_n_2774_, lean_object* v_projs_2775_, uint8_t v_globalDeclFound_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2766_, v_inst_2767_, v_inst_2768_, v_inst_2769_, v_inst_2770_, v_inst_2771_, v_view_2772_, v_findLocalDecl_x3f_2773_, v_n_2774_, v_projs_2775_, v_globalDeclFound_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2766_ = stack[1].m_obj;
lean_object* v_inst_2767_ = stack[2].m_obj;
lean_object* v_inst_2768_ = stack[3].m_obj;
lean_object* v_inst_2769_ = stack[4].m_obj;
lean_object* v_inst_2770_ = stack[5].m_obj;
lean_object* v_inst_2771_ = stack[6].m_obj;
lean_object* v_view_2772_ = stack[7].m_obj;
lean_object* v_findLocalDecl_x3f_2773_ = stack[8].m_obj;
lean_object* v_n_2774_ = stack[9].m_obj;
lean_object* v_projs_2775_ = stack[10].m_obj;
uint8_t v_globalDeclFound_2776_ = stack[11].m_num;
lean_object* v_res_2778_;
v_res_2778_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_box(0), v_inst_2766_, v_inst_2767_, v_inst_2768_, v_inst_2769_, v_inst_2770_, v_inst_2771_, v_view_2772_, v_findLocalDecl_x3f_2773_, v_n_2774_, v_projs_2775_, v_globalDeclFound_2776_);
stack->m_obj
 = v_res_2778_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_inst_2782_, lean_object* v_inst_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_view_2786_, lean_object* v_findLocalDecl_x3f_2787_, lean_object* v_n_2788_, lean_object* v_projs_2789_, lean_object* v_globalDeclFound_2790_){
_start:
{
uint8_t v_globalDeclFound_boxed_2791_; lean_object* v_res_2792_; 
v_globalDeclFound_boxed_2791_ = lean_unbox(v_globalDeclFound_2790_);
v_res_2792_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2779_, v_inst_2780_, v_inst_2781_, v_inst_2782_, v_inst_2783_, v_inst_2784_, v_inst_2785_, v_view_2786_, v_findLocalDecl_x3f_2787_, v_n_2788_, v_projs_2789_, v_globalDeclFound_boxed_2791_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2793_, lean_object* v_givenNameView_2794_, lean_object* v_fullDeclName_2795_, lean_object* v_ns_2796_){
_start:
{
lean_object* v_name_2797_; lean_object* v_imported_2798_; lean_object* v_ctx_2799_; lean_object* v_scopes_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v_name_2797_ = lean_ctor_get(v_givenNameView_2794_, 0);
v_imported_2798_ = lean_ctor_get(v_givenNameView_2794_, 1);
v_ctx_2799_ = lean_ctor_get(v_givenNameView_2794_, 2);
v_scopes_2800_ = lean_ctor_get(v_givenNameView_2794_, 3);
lean_inc(v_name_2797_);
lean_inc(v_ns_2796_);
v___x_2801_ = l_Lean_Name_append(v_ns_2796_, v_name_2797_);
lean_inc(v_scopes_2800_);
lean_inc(v_ctx_2799_);
lean_inc(v_imported_2798_);
v___x_2802_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v_imported_2798_);
lean_ctor_set(v___x_2802_, 2, v_ctx_2799_);
lean_ctor_set(v___x_2802_, 3, v_scopes_2800_);
v___x_2803_ = l_Lean_MacroScopesView_review(v___x_2802_);
v___x_2804_ = lean_name_eq(v___x_2803_, v_fullDeclName_2795_);
lean_dec(v___x_2803_);
if (v___x_2804_ == 0)
{
if (lean_obj_tag(v_ns_2796_) == 1)
{
lean_object* v_pre_2805_; 
v_pre_2805_ = lean_ctor_get(v_ns_2796_, 0);
lean_inc(v_pre_2805_);
lean_dec_ref_known(v_ns_2796_, 2);
v_ns_2796_ = v_pre_2805_;
goto _start;
}
else
{
lean_object* v___x_2807_; 
lean_dec(v_ns_2796_);
lean_dec_ref(v_givenNameView_2794_);
lean_dec_ref(v_localDecl_2793_);
v___x_2807_ = lean_box(0);
return v___x_2807_;
}
}
else
{
lean_object* v___x_2808_; 
lean_dec(v_ns_2796_);
lean_dec_ref(v_givenNameView_2794_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v_localDecl_2793_);
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2809_, lean_object* v_givenNameView_2810_, lean_object* v_fullDeclName_2811_, lean_object* v_ns_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2809_, v_givenNameView_2810_, v_fullDeclName_2811_, v_ns_2812_);
lean_dec(v_fullDeclName_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2814_, lean_object* v_givenName_2815_){
_start:
{
lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = l_Lean_LocalDecl_userName(v_localDecl_2814_);
v___x_2817_ = lean_name_eq(v___x_2816_, v_givenName_2815_);
lean_dec(v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec_ref(v_localDecl_2814_);
v___x_2818_ = lean_box(0);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_localDecl_2814_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2820_, lean_object* v_givenName_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2820_, v_givenName_2821_);
lean_dec(v_givenName_2821_);
return v_res_2822_;
}
}
lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2823_, lean_object* v_givenName_2824_, uint8_t v_skipAuxDecl_2825_, lean_object* v___f_2826_, lean_object* v_auxDeclToFullName_2827_, lean_object* v_currNamespace_2828_, lean_object* v_givenNameView_2829_, lean_object* v_x_2830_){
_start:
{
if (lean_obj_tag(v_x_2830_) == 0)
{
lean_dec_ref(v_givenNameView_2829_);
lean_dec(v_currNamespace_2828_);
lean_dec(v_auxDeclToFullName_2827_);
lean_dec_ref(v___f_2826_);
lean_dec(v_givenName_2824_);
lean_dec_ref(v_matchLocalDecl_x3f_2823_);
return v_x_2830_;
}
else
{
lean_object* v_val_2831_; uint8_t v___x_2832_; 
v_val_2831_ = lean_ctor_get(v_x_2830_, 0);
v___x_2832_ = l_Lean_LocalDecl_isAuxDecl(v_val_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
lean_inc(v_val_2831_);
lean_dec_ref_known(v_x_2830_, 1);
lean_dec_ref(v_givenNameView_2829_);
lean_dec(v_currNamespace_2828_);
lean_dec(v_auxDeclToFullName_2827_);
lean_dec_ref(v___f_2826_);
v___x_2833_ = lean_apply_2(v_matchLocalDecl_x3f_2823_, v_val_2831_, v_givenName_2824_);
return v___x_2833_;
}
else
{
if (v_skipAuxDecl_2825_ == 0)
{
if (v___x_2832_ == 0)
{
lean_object* v___x_2834_; 
lean_dec_ref_known(v_x_2830_, 1);
lean_dec_ref(v_givenNameView_2829_);
lean_dec(v_currNamespace_2828_);
lean_dec(v_auxDeclToFullName_2827_);
lean_dec_ref(v___f_2826_);
lean_dec(v_givenName_2824_);
lean_dec_ref(v_matchLocalDecl_x3f_2823_);
v___x_2834_ = lean_box(0);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = l_Lean_LocalDecl_fvarId(v_val_2831_);
v___x_2836_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2826_, v_auxDeclToFullName_2827_, v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 1)
{
lean_object* v_val_2837_; lean_object* v_fullDeclView_2838_; lean_object* v___y_2840_; lean_object* v_name_2861_; lean_object* v___x_2862_; 
lean_dec(v_givenName_2824_);
lean_dec_ref(v_matchLocalDecl_x3f_2823_);
v_val_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v_fullDeclView_2838_ = l_Lean_extractMacroScopes(v_val_2837_);
v_name_2861_ = lean_ctor_get(v_fullDeclView_2838_, 0);
lean_inc(v_name_2861_);
v___x_2862_ = l_Lean_privateToUserName_x3f(v_name_2861_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_inc(v_name_2861_);
v___y_2840_ = v_name_2861_;
goto v___jp_2839_;
}
else
{
lean_object* v_val_2863_; 
v_val_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___y_2840_ = v_val_2863_;
goto v___jp_2839_;
}
v___jp_2839_:
{
lean_object* v_imported_2841_; lean_object* v_ctx_2842_; lean_object* v_scopes_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2859_; 
v_imported_2841_ = lean_ctor_get(v_fullDeclView_2838_, 1);
v_ctx_2842_ = lean_ctor_get(v_fullDeclView_2838_, 2);
v_scopes_2843_ = lean_ctor_get(v_fullDeclView_2838_, 3);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_fullDeclView_2838_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v_fullDeclView_2838_, 0);
lean_dec(v_unused_2860_);
v___x_2845_ = v_fullDeclView_2838_;
v_isShared_2846_ = v_isSharedCheck_2859_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_scopes_2843_);
lean_inc(v_ctx_2842_);
lean_inc(v_imported_2841_);
lean_dec(v_fullDeclView_2838_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2859_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_fullDeclView_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___y_2840_);
v_fullDeclView_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___y_2840_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_imported_2841_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v_ctx_2842_);
lean_ctor_set(v_reuseFailAlloc_2858_, 3, v_scopes_2843_);
v_fullDeclView_2848_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v_fullDeclName_2849_; uint8_t v___x_2850_; 
lean_inc_ref(v_fullDeclView_2848_);
v_fullDeclName_2849_ = l_Lean_MacroScopesView_review(v_fullDeclView_2848_);
v___x_2850_ = l_Lean_Name_isPrefixOf(v_currNamespace_2828_, v_fullDeclName_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_inc(v_val_2831_);
lean_dec_ref(v_fullDeclView_2848_);
lean_dec_ref_known(v_x_2830_, 1);
v___x_2851_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2831_, v_givenNameView_2829_, v_fullDeclName_2849_, v_currNamespace_2828_);
lean_dec(v_fullDeclName_2849_);
return v___x_2851_;
}
else
{
lean_object* v___x_2852_; lean_object* v_localDeclNameView_2853_; uint8_t v___x_2854_; 
lean_dec(v_fullDeclName_2849_);
lean_dec(v_currNamespace_2828_);
v___x_2852_ = l_Lean_LocalDecl_userName(v_val_2831_);
v_localDeclNameView_2853_ = l_Lean_extractMacroScopes(v___x_2852_);
v___x_2854_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2853_, v_givenNameView_2829_);
lean_dec_ref(v_localDeclNameView_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v_fullDeclView_2848_);
lean_dec_ref_known(v_x_2830_, 1);
lean_dec_ref(v_givenNameView_2829_);
v___x_2855_ = lean_box(0);
return v___x_2855_;
}
else
{
uint8_t v___x_2856_; 
v___x_2856_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2829_, v_fullDeclView_2848_);
lean_dec_ref(v_fullDeclView_2848_);
lean_dec_ref(v_givenNameView_2829_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec_ref_known(v_x_2830_, 1);
v___x_2857_ = lean_box(0);
return v___x_2857_;
}
else
{
return v_x_2830_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2864_; 
lean_inc(v_val_2831_);
lean_dec(v___x_2836_);
lean_dec_ref_known(v_x_2830_, 1);
lean_dec_ref(v_givenNameView_2829_);
lean_dec(v_currNamespace_2828_);
v___x_2864_ = lean_apply_2(v_matchLocalDecl_x3f_2823_, v_val_2831_, v_givenName_2824_);
return v___x_2864_;
}
}
}
else
{
lean_object* v___x_2865_; 
lean_dec_ref_known(v_x_2830_, 1);
lean_dec_ref(v_givenNameView_2829_);
lean_dec(v_currNamespace_2828_);
lean_dec(v_auxDeclToFullName_2827_);
lean_dec_ref(v___f_2826_);
lean_dec(v_givenName_2824_);
lean_dec_ref(v_matchLocalDecl_x3f_2823_);
v___x_2865_ = lean_box(0);
return v___x_2865_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_resolveLocalName___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchLocalDecl_x3f_2823_ = stack[0].m_obj;
lean_object* v_givenName_2824_ = stack[1].m_obj;
uint8_t v_skipAuxDecl_2825_ = stack[2].m_num;
lean_object* v___f_2826_ = stack[3].m_obj;
lean_object* v_auxDeclToFullName_2827_ = stack[4].m_obj;
lean_object* v_currNamespace_2828_ = stack[5].m_obj;
lean_object* v_givenNameView_2829_ = stack[6].m_obj;
lean_object* v_x_2830_ = stack[7].m_obj;
lean_object* v_res_2866_;
v_res_2866_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2823_, v_givenName_2824_, v_skipAuxDecl_2825_, v___f_2826_, v_auxDeclToFullName_2827_, v_currNamespace_2828_, v_givenNameView_2829_, v_x_2830_);
stack->m_obj
 = v_res_2866_;
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2867_, lean_object* v_givenName_2868_, lean_object* v_skipAuxDecl_2869_, lean_object* v___f_2870_, lean_object* v_auxDeclToFullName_2871_, lean_object* v_currNamespace_2872_, lean_object* v_givenNameView_2873_, lean_object* v_x_2874_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2875_; lean_object* v_res_2876_; 
v_skipAuxDecl_boxed_2875_ = lean_unbox(v_skipAuxDecl_2869_);
v_res_2876_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2867_, v_givenName_2868_, v_skipAuxDecl_boxed_2875_, v___f_2870_, v_auxDeclToFullName_2871_, v_currNamespace_2872_, v_givenNameView_2873_, v_x_2874_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2877_, lean_object* v_matchLocalDecl_x3f_2878_, lean_object* v_givenName_2879_, lean_object* v_x_2880_){
_start:
{
if (lean_obj_tag(v_x_2880_) == 0)
{
lean_dec(v_givenName_2879_);
lean_dec_ref(v_matchLocalDecl_x3f_2878_);
return v_x_2880_;
}
else
{
lean_object* v_val_2881_; uint8_t v___x_2882_; 
v_val_2881_ = lean_ctor_get(v_x_2880_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_x_2880_, 1);
v___x_2882_ = l_Lean_LocalDecl_isAuxDecl(v_val_2881_);
if (v___x_2882_ == 0)
{
lean_dec(v_val_2881_);
lean_dec(v_givenName_2879_);
lean_dec_ref(v_matchLocalDecl_x3f_2878_);
lean_inc(v_localDecl_x3f_2877_);
return v_localDecl_x3f_2877_;
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_apply_2(v_matchLocalDecl_x3f_2878_, v_val_2881_, v_givenName_2879_);
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2884_, lean_object* v_matchLocalDecl_x3f_2885_, lean_object* v_givenName_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2884_, v_matchLocalDecl_x3f_2885_, v_givenName_2886_, v_x_2887_);
lean_dec(v_localDecl_x3f_2884_);
return v_res_2888_;
}
}
lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2908_, lean_object* v_matchLocalDecl_x3f_2909_, lean_object* v___f_2910_, lean_object* v_auxDeclToFullName_2911_, lean_object* v_currNamespace_2912_, lean_object* v_givenNameView_2913_, uint8_t v_skipAuxDecl_2914_){
_start:
{
lean_object* v_decls_2915_; lean_object* v_givenName_2916_; lean_object* v___x_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; lean_object* v_localDecl_x3f_2920_; 
v_decls_2915_ = lean_ctor_get(v_lctx_2908_, 1);
lean_inc_ref_n(v_decls_2915_, 2);
lean_dec_ref(v_lctx_2908_);
lean_inc_ref(v_givenNameView_2913_);
v_givenName_2916_ = l_Lean_MacroScopesView_review(v_givenNameView_2913_);
v___x_2917_ = lean_box(v_skipAuxDecl_2914_);
lean_inc(v_givenName_2916_);
lean_inc_ref(v_matchLocalDecl_x3f_2909_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2918_, 0, v_matchLocalDecl_x3f_2909_);
lean_closure_set(v___f_2918_, 1, v_givenName_2916_);
lean_closure_set(v___f_2918_, 2, v___x_2917_);
lean_closure_set(v___f_2918_, 3, v___f_2910_);
lean_closure_set(v___f_2918_, 4, v_auxDeclToFullName_2911_);
lean_closure_set(v___f_2918_, 5, v_currNamespace_2912_);
lean_closure_set(v___f_2918_, 6, v_givenNameView_2913_);
v___x_2919_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2920_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2919_, v_decls_2915_, v___f_2918_);
if (lean_obj_tag(v_localDecl_x3f_2920_) == 0)
{
if (v_skipAuxDecl_2914_ == 0)
{
lean_object* v___f_2921_; lean_object* v___x_2922_; 
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2921_, 0, v_localDecl_x3f_2920_);
lean_closure_set(v___f_2921_, 1, v_matchLocalDecl_x3f_2909_);
lean_closure_set(v___f_2921_, 2, v_givenName_2916_);
v___x_2922_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2919_, v_decls_2915_, v___f_2921_);
return v___x_2922_;
}
else
{
lean_dec(v_givenName_2916_);
lean_dec_ref(v_decls_2915_);
lean_dec_ref(v_matchLocalDecl_x3f_2909_);
return v_localDecl_x3f_2920_;
}
}
else
{
lean_dec(v_givenName_2916_);
lean_dec_ref(v_decls_2915_);
lean_dec_ref(v_matchLocalDecl_x3f_2909_);
return v_localDecl_x3f_2920_;
}
}
}
LEAN_EXPORT void l_Lean_resolveLocalName___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2908_ = stack[0].m_obj;
lean_object* v_matchLocalDecl_x3f_2909_ = stack[1].m_obj;
lean_object* v___f_2910_ = stack[2].m_obj;
lean_object* v_auxDeclToFullName_2911_ = stack[3].m_obj;
lean_object* v_currNamespace_2912_ = stack[4].m_obj;
lean_object* v_givenNameView_2913_ = stack[5].m_obj;
uint8_t v_skipAuxDecl_2914_ = stack[6].m_num;
lean_object* v_res_2923_;
v_res_2923_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2908_, v_matchLocalDecl_x3f_2909_, v___f_2910_, v_auxDeclToFullName_2911_, v_currNamespace_2912_, v_givenNameView_2913_, v_skipAuxDecl_2914_);
stack->m_obj
 = v_res_2923_;
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2924_, lean_object* v_matchLocalDecl_x3f_2925_, lean_object* v___f_2926_, lean_object* v_auxDeclToFullName_2927_, lean_object* v_currNamespace_2928_, lean_object* v_givenNameView_2929_, lean_object* v_skipAuxDecl_2930_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2931_; lean_object* v_res_2932_; 
v_skipAuxDecl_boxed_2931_ = lean_unbox(v_skipAuxDecl_2930_);
v_res_2932_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2924_, v_matchLocalDecl_x3f_2925_, v___f_2926_, v_auxDeclToFullName_2927_, v_currNamespace_2928_, v_givenNameView_2929_, v_skipAuxDecl_boxed_2931_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2933_, lean_object* v_lctx_2934_, lean_object* v_matchLocalDecl_x3f_2935_, lean_object* v___f_2936_, lean_object* v_auxDeclToFullName_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_currNamespace_2944_){
_start:
{
lean_object* v_view_2945_; lean_object* v_name_2946_; lean_object* v_findLocalDecl_x3f_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; lean_object* v___x_2950_; 
v_view_2945_ = l_Lean_extractMacroScopes(v_n_2933_);
v_name_2946_ = lean_ctor_get(v_view_2945_, 0);
lean_inc(v_name_2946_);
v_findLocalDecl_x3f_2947_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2947_, 0, v_lctx_2934_);
lean_closure_set(v_findLocalDecl_x3f_2947_, 1, v_matchLocalDecl_x3f_2935_);
lean_closure_set(v_findLocalDecl_x3f_2947_, 2, v___f_2936_);
lean_closure_set(v_findLocalDecl_x3f_2947_, 3, v_auxDeclToFullName_2937_);
lean_closure_set(v_findLocalDecl_x3f_2947_, 4, v_currNamespace_2944_);
v___x_2948_ = lean_box(0);
v___x_2949_ = 0;
v___x_2950_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2938_, v_inst_2939_, v_inst_2940_, v_inst_2941_, v_inst_2942_, v_inst_2943_, v_view_2945_, v_findLocalDecl_x3f_2947_, v_name_2946_, v___x_2948_, v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2951_, lean_object* v_n_2952_, lean_object* v_lctx_2953_, lean_object* v_matchLocalDecl_x3f_2954_, lean_object* v___f_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_toBind_2961_, lean_object* v_____do__lift_2962_){
_start:
{
lean_object* v_auxDeclToFullName_2963_; lean_object* v_getCurrNamespace_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; 
v_auxDeclToFullName_2963_ = lean_ctor_get(v_____do__lift_2962_, 2);
lean_inc(v_auxDeclToFullName_2963_);
lean_dec_ref(v_____do__lift_2962_);
v_getCurrNamespace_2964_ = lean_ctor_get(v_inst_2951_, 0);
lean_inc(v_getCurrNamespace_2964_);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2965_, 0, v_n_2952_);
lean_closure_set(v___f_2965_, 1, v_lctx_2953_);
lean_closure_set(v___f_2965_, 2, v_matchLocalDecl_x3f_2954_);
lean_closure_set(v___f_2965_, 3, v___f_2955_);
lean_closure_set(v___f_2965_, 4, v_auxDeclToFullName_2963_);
lean_closure_set(v___f_2965_, 5, v_inst_2956_);
lean_closure_set(v___f_2965_, 6, v_inst_2951_);
lean_closure_set(v___f_2965_, 7, v_inst_2957_);
lean_closure_set(v___f_2965_, 8, v_inst_2958_);
lean_closure_set(v___f_2965_, 9, v_inst_2959_);
lean_closure_set(v___f_2965_, 10, v_inst_2960_);
v___x_2966_ = lean_apply_4(v_toBind_2961_, lean_box(0), lean_box(0), v_getCurrNamespace_2964_, v___f_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2967_, lean_object* v_n_2968_, lean_object* v_matchLocalDecl_x3f_2969_, lean_object* v___f_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_toBind_2976_, lean_object* v_inst_2977_, lean_object* v_lctx_2978_){
_start:
{
lean_object* v___f_2979_; lean_object* v___x_2980_; 
lean_inc(v_toBind_2976_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2979_, 0, v_inst_2967_);
lean_closure_set(v___f_2979_, 1, v_n_2968_);
lean_closure_set(v___f_2979_, 2, v_lctx_2978_);
lean_closure_set(v___f_2979_, 3, v_matchLocalDecl_x3f_2969_);
lean_closure_set(v___f_2979_, 4, v___f_2970_);
lean_closure_set(v___f_2979_, 5, v_inst_2971_);
lean_closure_set(v___f_2979_, 6, v_inst_2972_);
lean_closure_set(v___f_2979_, 7, v_inst_2973_);
lean_closure_set(v___f_2979_, 8, v_inst_2974_);
lean_closure_set(v___f_2979_, 9, v_inst_2975_);
lean_closure_set(v___f_2979_, 10, v_toBind_2976_);
v___x_2980_ = lean_apply_4(v_toBind_2976_, lean_box(0), lean_box(0), v_inst_2977_, v___f_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_n_2990_){
_start:
{
lean_object* v_toBind_2991_; lean_object* v___f_2992_; lean_object* v_matchLocalDecl_x3f_2993_; lean_object* v___f_2994_; lean_object* v___x_2995_; 
v_toBind_2991_ = lean_ctor_get(v_inst_2983_, 1);
lean_inc_n(v_toBind_2991_, 2);
v___f_2992_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2993_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2989_);
v___f_2994_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2994_, 0, v_inst_2984_);
lean_closure_set(v___f_2994_, 1, v_n_2990_);
lean_closure_set(v___f_2994_, 2, v_matchLocalDecl_x3f_2993_);
lean_closure_set(v___f_2994_, 3, v___f_2992_);
lean_closure_set(v___f_2994_, 4, v_inst_2983_);
lean_closure_set(v___f_2994_, 5, v_inst_2985_);
lean_closure_set(v___f_2994_, 6, v_inst_2986_);
lean_closure_set(v___f_2994_, 7, v_inst_2987_);
lean_closure_set(v___f_2994_, 8, v_inst_2988_);
lean_closure_set(v___f_2994_, 9, v_toBind_2991_);
lean_closure_set(v___f_2994_, 10, v_inst_2989_);
v___x_2995_ = lean_apply_4(v_toBind_2991_, lean_box(0), lean_box(0), v_inst_2989_, v___f_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_n_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_resolveLocalName___redArg(v_inst_2997_, v_inst_2998_, v_inst_2999_, v_inst_3000_, v_inst_3001_, v_inst_3002_, v_inst_3003_, v_n_3004_);
return v___x_3005_;
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_3006_, uint8_t v_____do__lift_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_box(v_____do__lift_3007_);
v___x_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
v___x_3010_ = lean_apply_2(v_toPure_3006_, lean_box(0), v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3006_ = stack[0].m_obj;
uint8_t v_____do__lift_3007_ = stack[1].m_num;
lean_object* v_res_3011_;
v_res_3011_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_3006_, v_____do__lift_3007_);
stack->m_obj
 = v_res_3011_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_3012_, lean_object* v_____do__lift_3013_){
_start:
{
uint8_t v_____do__lift_1060__boxed_3014_; lean_object* v_res_3015_; 
v_____do__lift_1060__boxed_3014_ = lean_unbox(v_____do__lift_3013_);
v_res_3015_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_3012_, v_____do__lift_1060__boxed_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_3016_, lean_object* v___y_3017_, lean_object* v_____do__lift_3018_){
_start:
{
if (lean_obj_tag(v_____do__lift_3018_) == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec(v___y_3017_);
v___x_3019_ = lean_box(0);
v___x_3020_ = lean_apply_2(v_toPure_3016_, lean_box(0), v___x_3019_);
return v___x_3020_;
}
else
{
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3028_; 
v_isSharedCheck_3028_ = !lean_is_exclusive(v_____do__lift_3018_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v_____do__lift_3018_, 0);
lean_dec(v_unused_3029_);
v___x_3022_ = v_____do__lift_3018_;
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v_____do__lift_3018_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___y_3017_);
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___y_3017_);
v___x_3025_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_apply_2(v_toPure_3016_, lean_box(0), v___x_3025_);
return v___x_3026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_3032_, lean_object* v_toBind_3033_, lean_object* v___f_3034_, lean_object* v_____do__lift_3035_){
_start:
{
if (lean_obj_tag(v_____do__lift_3035_) == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec(v___f_3034_);
lean_dec(v_toBind_3033_);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_apply_2(v_toPure_3032_, lean_box(0), v___x_3036_);
return v___x_3037_;
}
else
{
lean_object* v_val_3038_; uint8_t v___x_3039_; 
v_val_3038_ = lean_ctor_get(v_____do__lift_3035_, 0);
v___x_3039_ = lean_unbox(v_val_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_apply_2(v_toPure_3032_, lean_box(0), v___x_3040_);
v___x_3042_ = lean_apply_4(v_toBind_3033_, lean_box(0), lean_box(0), v___x_3041_, v___f_3034_);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3044_ = lean_apply_2(v_toPure_3032_, lean_box(0), v___x_3043_);
v___x_3045_ = lean_apply_4(v_toBind_3033_, lean_box(0), lean_box(0), v___x_3044_, v___f_3034_);
return v___x_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_3046_, lean_object* v_toBind_3047_, lean_object* v___f_3048_, lean_object* v_____do__lift_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_3046_, v_toBind_3047_, v___f_3048_, v_____do__lift_3049_);
lean_dec(v_____do__lift_3049_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_3051_, lean_object* v_filter_3052_, lean_object* v___y_3053_, lean_object* v_toBind_3054_, lean_object* v___f_3055_, lean_object* v___f_3056_, lean_object* v_____do__lift_3057_){
_start:
{
if (lean_obj_tag(v_____do__lift_3057_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_dec(v___f_3056_);
lean_dec(v___f_3055_);
lean_dec(v_toBind_3054_);
lean_dec(v___y_3053_);
lean_dec(v_filter_3052_);
v___x_3058_ = lean_box(0);
v___x_3059_ = lean_apply_2(v_toPure_3051_, lean_box(0), v___x_3058_);
return v___x_3059_;
}
else
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v_toPure_3051_);
v___x_3060_ = lean_apply_1(v_filter_3052_, v___y_3053_);
lean_inc(v_toBind_3054_);
v___x_3061_ = lean_apply_4(v_toBind_3054_, lean_box(0), lean_box(0), v___x_3060_, v___f_3055_);
v___x_3062_ = lean_apply_4(v_toBind_3054_, lean_box(0), lean_box(0), v___x_3061_, v___f_3056_);
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3063_, lean_object* v_filter_3064_, lean_object* v___y_3065_, lean_object* v_toBind_3066_, lean_object* v___f_3067_, lean_object* v___f_3068_, lean_object* v_____do__lift_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3063_, v_filter_3064_, v___y_3065_, v_toBind_3066_, v___f_3067_, v___f_3068_, v_____do__lift_3069_);
lean_dec(v_____do__lift_3069_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3071_, lean_object* v_n_u2080_3072_, lean_object* v_toBind_3073_, lean_object* v___f_3074_, lean_object* v_____do__lift_3075_){
_start:
{
if (lean_obj_tag(v_____do__lift_3075_) == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_dec(v___f_3074_);
lean_dec(v_toBind_3073_);
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_apply_2(v_toPure_3071_, lean_box(0), v___x_3079_);
return v___x_3080_;
}
else
{
lean_object* v_val_3081_; 
v_val_3081_ = lean_ctor_get(v_____do__lift_3075_, 0);
if (lean_obj_tag(v_val_3081_) == 1)
{
lean_object* v_tail_3082_; 
v_tail_3082_ = lean_ctor_get(v_val_3081_, 1);
if (lean_obj_tag(v_tail_3082_) == 0)
{
lean_object* v_head_3083_; lean_object* v_fst_3084_; uint8_t v___x_3085_; 
v_head_3083_ = lean_ctor_get(v_val_3081_, 0);
v_fst_3084_ = lean_ctor_get(v_head_3083_, 0);
v___x_3085_ = lean_name_eq(v_fst_3084_, v_n_u2080_3072_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_apply_2(v_toPure_3071_, lean_box(0), v___x_3086_);
v___x_3088_ = lean_apply_4(v_toBind_3073_, lean_box(0), lean_box(0), v___x_3087_, v___f_3074_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3090_ = lean_apply_2(v_toPure_3071_, lean_box(0), v___x_3089_);
v___x_3091_ = lean_apply_4(v_toBind_3073_, lean_box(0), lean_box(0), v___x_3090_, v___f_3074_);
return v___x_3091_;
}
}
else
{
lean_dec(v___f_3074_);
lean_dec(v_toBind_3073_);
goto v___jp_3076_;
}
}
else
{
lean_dec(v___f_3074_);
lean_dec(v_toBind_3073_);
goto v___jp_3076_;
}
}
v___jp_3076_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_apply_2(v_toPure_3071_, lean_box(0), v___x_3077_);
return v___x_3078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3092_, lean_object* v_n_u2080_3093_, lean_object* v_toBind_3094_, lean_object* v___f_3095_, lean_object* v_____do__lift_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3092_, v_n_u2080_3093_, v_toBind_3094_, v___f_3095_, v_____do__lift_3096_);
lean_dec(v_____do__lift_3096_);
lean_dec(v_n_u2080_3093_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_n_u2080_3104_, lean_object* v_filter_3105_, lean_object* v_view_x3f_3106_, lean_object* v_n_3107_){
_start:
{
lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___f_3110_; lean_object* v___f_3111_; lean_object* v___f_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v_toApplicative_3120_; lean_object* v_getEnv_3121_; lean_object* v_modifyEnv_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3160_; 
lean_inc_ref_n(v_inst_3098_, 8);
v___f_3108_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3108_, 0, v_inst_3098_);
v___f_3109_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3109_, 0, v_inst_3098_);
v___f_3110_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3110_, 0, v_inst_3098_);
v___f_3111_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3111_, 0, v_inst_3098_);
v___f_3112_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3112_, 0, v_inst_3098_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___f_3108_);
lean_ctor_set(v___x_3113_, 1, v___f_3109_);
v___x_3114_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3114_, 0, lean_box(0));
lean_closure_set(v___x_3114_, 1, v_inst_3098_);
v___x_3115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
lean_ctor_set(v___x_3115_, 2, v___f_3110_);
lean_ctor_set(v___x_3115_, 3, v___f_3111_);
lean_ctor_set(v___x_3115_, 4, v___f_3112_);
v___x_3116_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3116_, 0, lean_box(0));
lean_closure_set(v___x_3116_, 1, v_inst_3098_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3118_, 0, lean_box(0));
lean_closure_set(v___x_3118_, 1, v_inst_3098_);
lean_inc_ref(v___x_3118_);
v___x_3119_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3118_, v_inst_3099_);
v_toApplicative_3120_ = lean_ctor_get(v_inst_3098_, 0);
lean_inc_ref(v_toApplicative_3120_);
v_getEnv_3121_ = lean_ctor_get(v_inst_3100_, 0);
v_modifyEnv_3122_ = lean_ctor_get(v_inst_3100_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_inst_3100_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3124_ = v_inst_3100_;
v_isShared_3125_ = v_isSharedCheck_3160_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_modifyEnv_3122_);
lean_inc(v_getEnv_3121_);
lean_dec(v_inst_3100_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3160_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v_toBind_3126_; lean_object* v_toPure_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v_toBind_3126_ = lean_ctor_get(v_inst_3098_, 1);
lean_inc_n(v_toBind_3126_, 2);
lean_dec_ref(v_inst_3098_);
v_toPure_3127_ = lean_ctor_get(v_toApplicative_3120_, 1);
lean_inc_n(v_toPure_3127_, 3);
lean_dec_ref(v_toApplicative_3120_);
lean_inc_ref(v___x_3118_);
v___f_3128_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3128_, 0, v_modifyEnv_3122_);
lean_closure_set(v___f_3128_, 1, v___x_3118_);
v___f_3129_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3129_, 0, v_toPure_3127_);
v___f_3130_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3130_, 0, v_toPure_3127_);
v___x_3131_ = lean_apply_4(v_toBind_3126_, lean_box(0), lean_box(0), v_getEnv_3121_, v___f_3130_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 1, v___f_3128_);
lean_ctor_set(v___x_3124_, 0, v___x_3131_);
v___x_3133_ = v___x_3124_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___f_3128_);
v___x_3133_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___f_3136_; lean_object* v___y_3138_; 
lean_inc_ref_n(v___x_3118_, 2);
v___x_3134_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_3118_, v_inst_3101_);
v___x_3135_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3118_, v_inst_3102_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3136_, 0, v_inst_3103_);
lean_closure_set(v___f_3136_, 1, v___x_3118_);
if (lean_obj_tag(v_view_x3f_3106_) == 1)
{
lean_object* v_val_3146_; lean_object* v_imported_3147_; lean_object* v_ctx_3148_; lean_object* v_scopes_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3157_; 
v_val_3146_ = lean_ctor_get(v_view_x3f_3106_, 0);
lean_inc(v_val_3146_);
lean_dec_ref_known(v_view_x3f_3106_, 1);
v_imported_3147_ = lean_ctor_get(v_val_3146_, 1);
v_ctx_3148_ = lean_ctor_get(v_val_3146_, 2);
v_scopes_3149_ = lean_ctor_get(v_val_3146_, 3);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_val_3146_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v_val_3146_, 0);
lean_dec(v_unused_3158_);
v___x_3151_ = v_val_3146_;
v_isShared_3152_ = v_isSharedCheck_3157_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_scopes_3149_);
lean_inc(v_ctx_3148_);
lean_inc(v_imported_3147_);
lean_dec(v_val_3146_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3157_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v_n_3107_);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_n_3107_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_imported_3147_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_ctx_3148_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_scopes_3149_);
v___x_3154_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_MacroScopesView_review(v___x_3154_);
v___y_3138_ = v___x_3155_;
goto v___jp_3137_;
}
}
}
else
{
lean_dec(v_view_x3f_3106_);
v___y_3138_ = v_n_3107_;
goto v___jp_3137_;
}
v___jp_3137_:
{
lean_object* v___f_3139_; lean_object* v___f_3140_; lean_object* v___f_3141_; lean_object* v___f_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_inc_n(v___y_3138_, 2);
lean_inc_n(v_toPure_3127_, 3);
v___f_3139_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3139_, 0, v_toPure_3127_);
lean_closure_set(v___f_3139_, 1, v___y_3138_);
lean_inc_n(v_toBind_3126_, 3);
v___f_3140_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3140_, 0, v_toPure_3127_);
lean_closure_set(v___f_3140_, 1, v_toBind_3126_);
lean_closure_set(v___f_3140_, 2, v___f_3139_);
v___f_3141_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3141_, 0, v_toPure_3127_);
lean_closure_set(v___f_3141_, 1, v_filter_3105_);
lean_closure_set(v___f_3141_, 2, v___y_3138_);
lean_closure_set(v___f_3141_, 3, v_toBind_3126_);
lean_closure_set(v___f_3141_, 4, v___f_3129_);
lean_closure_set(v___f_3141_, 5, v___f_3140_);
v___f_3142_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3142_, 0, v_toPure_3127_);
lean_closure_set(v___f_3142_, 1, v_n_u2080_3104_);
lean_closure_set(v___f_3142_, 2, v_toBind_3126_);
lean_closure_set(v___f_3142_, 3, v___f_3141_);
v___x_3143_ = 0;
v___x_3144_ = l_Lean_resolveGlobalName___redArg(v___x_3117_, v___x_3119_, v___x_3133_, v___x_3134_, v___x_3135_, v___f_3136_, v___y_3138_, v___x_3143_);
v___x_3145_ = lean_apply_4(v_toBind_3126_, lean_box(0), lean_box(0), v___x_3144_, v___f_3142_);
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_n_u2080_3168_, lean_object* v_filter_3169_, lean_object* v_view_x3f_3170_, lean_object* v_n_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3162_, v_inst_3163_, v_inst_3164_, v_inst_3165_, v_inst_3166_, v_inst_3167_, v_n_u2080_3168_, v_filter_3169_, v_view_x3f_3170_, v_n_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3177_, lean_object* v_____x_3178_){
_start:
{
if (lean_obj_tag(v_____x_3178_) == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3180_ = lean_apply_2(v_toPure_3177_, lean_box(0), v___x_3179_);
return v___x_3180_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_apply_2(v_toPure_3177_, lean_box(0), v_____x_3178_);
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3182_, lean_object* v_____do__lift_3183_){
_start:
{
if (lean_obj_tag(v_____do__lift_3183_) == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_apply_2(v_toPure_3182_, lean_box(0), v___x_3184_);
return v___x_3185_;
}
else
{
lean_object* v_val_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3195_; 
v_val_3186_ = lean_ctor_get(v_____do__lift_3183_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_____do__lift_3183_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3188_ = v_____do__lift_3183_;
v_isShared_3189_ = v_isSharedCheck_3195_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_val_3186_);
lean_dec(v_____do__lift_3183_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3195_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_val_3186_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_apply_2(v_toPure_3182_, lean_box(0), v___x_3192_);
return v___x_3193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3196_, lean_object* v___x_3197_, lean_object* v_____do__lift_3198_){
_start:
{
if (lean_obj_tag(v_____do__lift_3198_) == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = lean_apply_2(v_toPure_3196_, lean_box(0), v___x_3197_);
return v___x_3199_;
}
else
{
lean_object* v_val_3200_; lean_object* v_fst_3201_; lean_object* v___x_3202_; 
lean_dec(v___x_3197_);
v_val_3200_ = lean_ctor_get(v_____do__lift_3198_, 0);
lean_inc(v_val_3200_);
lean_dec_ref_known(v_____do__lift_3198_, 1);
v_fst_3201_ = lean_ctor_get(v_val_3200_, 0);
lean_inc(v_fst_3201_);
lean_dec(v_val_3200_);
v___x_3202_ = lean_apply_2(v_toPure_3196_, lean_box(0), v_fst_3201_);
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3203_, lean_object* v___x_3204_, lean_object* v___x_3205_, lean_object* v_____do__lift_3206_){
_start:
{
if (lean_obj_tag(v_____do__lift_3206_) == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v___x_3205_);
lean_dec(v___x_3204_);
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_apply_2(v_toPure_3203_, lean_box(0), v___x_3207_);
return v___x_3208_;
}
else
{
lean_object* v_val_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3240_; 
v_val_3209_ = lean_ctor_get(v_____do__lift_3206_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_____do__lift_3206_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3211_ = v_____do__lift_3206_;
v_isShared_3212_ = v_isSharedCheck_3240_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_val_3209_);
lean_dec(v_____do__lift_3206_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3240_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
if (lean_obj_tag(v_val_3209_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v___x_3205_);
v_a_3213_ = lean_ctor_get(v_val_3209_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_val_3209_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3215_ = v_val_3209_;
v_isShared_3216_ = v_isSharedCheck_3226_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v_val_3209_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3226_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v_a_3213_);
v___x_3218_ = v___x_3211_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v___x_3204_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3219_);
v___x_3221_ = v___x_3215_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v___x_3223_ = lean_apply_2(v_toPure_3203_, lean_box(0), v___x_3222_);
return v___x_3223_;
}
}
}
}
else
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3238_; 
v_isSharedCheck_3238_ = !lean_is_exclusive(v_val_3209_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_val_3209_, 0);
lean_dec(v_unused_3239_);
v___x_3228_ = v_val_3209_;
v_isShared_3229_ = v_isSharedCheck_3238_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v_val_3209_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3238_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3205_);
lean_ctor_set(v___x_3230_, 1, v___x_3204_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3230_);
v___x_3232_ = v___x_3228_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3232_);
v___x_3234_ = v___x_3211_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_apply_2(v_toPure_3203_, lean_box(0), v___x_3234_);
return v___x_3235_;
}
}
}
}
}
}
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3241_, lean_object* v___x_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_n_u2080_3249_, lean_object* v_filter_3250_, lean_object* v_view_x3f_3251_, lean_object* v_toBind_3252_, lean_object* v___f_3253_, lean_object* v___f_3254_, lean_object* v_a_3255_, lean_object* v_x_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_snd_3258_; lean_object* v___x_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_snd_3258_ = lean_ctor_get(v___y_3257_, 1);
lean_inc(v_snd_3258_);
lean_dec_ref(v___y_3257_);
v___x_3259_ = l_Lean_Name_appendCore(v_a_3255_, v_snd_3258_);
lean_inc(v___x_3259_);
v___f_3260_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3260_, 0, v_toPure_3241_);
lean_closure_set(v___f_3260_, 1, v___x_3259_);
lean_closure_set(v___f_3260_, 2, v___x_3242_);
v___x_3261_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3243_, v_inst_3244_, v_inst_3245_, v_inst_3246_, v_inst_3247_, v_inst_3248_, v_n_u2080_3249_, v_filter_3250_, v_view_x3f_3251_, v___x_3259_);
lean_inc_n(v_toBind_3252_, 2);
v___x_3262_ = lean_apply_4(v_toBind_3252_, lean_box(0), lean_box(0), v___x_3261_, v___f_3253_);
v___x_3263_ = lean_apply_4(v_toBind_3252_, lean_box(0), lean_box(0), v___x_3262_, v___f_3254_);
v___x_3264_ = lean_apply_4(v_toBind_3252_, lean_box(0), lean_box(0), v___x_3263_, v___f_3260_);
return v___x_3264_;
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3241_ = stack[0].m_obj;
lean_object* v___x_3242_ = stack[1].m_obj;
lean_object* v_inst_3243_ = stack[2].m_obj;
lean_object* v_inst_3244_ = stack[3].m_obj;
lean_object* v_inst_3245_ = stack[4].m_obj;
lean_object* v_inst_3246_ = stack[5].m_obj;
lean_object* v_inst_3247_ = stack[6].m_obj;
lean_object* v_inst_3248_ = stack[7].m_obj;
lean_object* v_n_u2080_3249_ = stack[8].m_obj;
lean_object* v_filter_3250_ = stack[9].m_obj;
lean_object* v_view_x3f_3251_ = stack[10].m_obj;
lean_object* v_toBind_3252_ = stack[11].m_obj;
lean_object* v___f_3253_ = stack[12].m_obj;
lean_object* v___f_3254_ = stack[13].m_obj;
lean_object* v_a_3255_ = stack[14].m_obj;
lean_object* v___y_3257_ = stack[16].m_obj;
lean_object* v_res_3265_;
v_res_3265_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3241_, v___x_3242_, v_inst_3243_, v_inst_3244_, v_inst_3245_, v_inst_3246_, v_inst_3247_, v_inst_3248_, v_n_u2080_3249_, v_filter_3250_, v_view_x3f_3251_, v_toBind_3252_, v___f_3253_, v___f_3254_, v_a_3255_, lean_box(0), v___y_3257_);
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3266_ = _args[0];
lean_object* v___x_3267_ = _args[1];
lean_object* v_inst_3268_ = _args[2];
lean_object* v_inst_3269_ = _args[3];
lean_object* v_inst_3270_ = _args[4];
lean_object* v_inst_3271_ = _args[5];
lean_object* v_inst_3272_ = _args[6];
lean_object* v_inst_3273_ = _args[7];
lean_object* v_n_u2080_3274_ = _args[8];
lean_object* v_filter_3275_ = _args[9];
lean_object* v_view_x3f_3276_ = _args[10];
lean_object* v_toBind_3277_ = _args[11];
lean_object* v___f_3278_ = _args[12];
lean_object* v___f_3279_ = _args[13];
lean_object* v_a_3280_ = _args[14];
lean_object* v_x_3281_ = _args[15];
lean_object* v___y_3282_ = _args[16];
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3266_, v___x_3267_, v_inst_3268_, v_inst_3269_, v_inst_3270_, v_inst_3271_, v_inst_3272_, v_inst_3273_, v_n_u2080_3274_, v_filter_3275_, v_view_x3f_3276_, v_toBind_3277_, v___f_3278_, v___f_3279_, v_a_3280_, v_x_3281_, v___y_3282_);
lean_dec(v_a_3280_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3287_, lean_object* v_n_3288_, lean_object* v_inst_3289_, lean_object* v_inst_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_inst_3294_, lean_object* v_n_u2080_3295_, lean_object* v_filter_3296_, lean_object* v_view_x3f_3297_, lean_object* v_toBind_3298_, lean_object* v___f_3299_, lean_object* v___f_3300_, lean_object* v___x_3301_, lean_object* v_____do__lift_3302_){
_start:
{
if (lean_obj_tag(v_____do__lift_3302_) == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref(v___x_3301_);
lean_dec(v___f_3300_);
lean_dec(v___f_3299_);
lean_dec(v_toBind_3298_);
lean_dec(v_view_x3f_3297_);
lean_dec(v_filter_3296_);
lean_dec(v_n_u2080_3295_);
lean_dec(v_inst_3294_);
lean_dec_ref(v_inst_3293_);
lean_dec_ref(v_inst_3292_);
lean_dec_ref(v_inst_3291_);
lean_dec_ref(v_inst_3290_);
lean_dec_ref(v_inst_3289_);
lean_dec(v_n_3288_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_apply_2(v_toPure_3287_, lean_box(0), v___x_3303_);
return v___x_3304_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3305_ = l_Lean_privateToUserName(v_n_3288_);
v___x_3306_ = l_Lean_Name_componentsRev(v___x_3305_);
v___x_3307_ = lean_box(0);
lean_inc(v_toPure_3287_);
v___f_3308_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3308_, 0, v_toPure_3287_);
lean_closure_set(v___f_3308_, 1, v___x_3307_);
lean_inc(v_toBind_3298_);
v___f_3309_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3309_, 0, v_toPure_3287_);
lean_closure_set(v___f_3309_, 1, v___x_3307_);
lean_closure_set(v___f_3309_, 2, v_inst_3289_);
lean_closure_set(v___f_3309_, 3, v_inst_3290_);
lean_closure_set(v___f_3309_, 4, v_inst_3291_);
lean_closure_set(v___f_3309_, 5, v_inst_3292_);
lean_closure_set(v___f_3309_, 6, v_inst_3293_);
lean_closure_set(v___f_3309_, 7, v_inst_3294_);
lean_closure_set(v___f_3309_, 8, v_n_u2080_3295_);
lean_closure_set(v___f_3309_, 9, v_filter_3296_);
lean_closure_set(v___f_3309_, 10, v_view_x3f_3297_);
lean_closure_set(v___f_3309_, 11, v_toBind_3298_);
lean_closure_set(v___f_3309_, 12, v___f_3299_);
lean_closure_set(v___f_3309_, 13, v___f_3300_);
v___x_3310_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3311_ = l_List_forIn_x27_loop___redArg(v___x_3301_, v___f_3309_, v___x_3306_, v___x_3310_);
lean_dec(v___x_3306_);
v___x_3312_ = lean_apply_4(v_toBind_3298_, lean_box(0), lean_box(0), v___x_3311_, v___f_3308_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3313_, lean_object* v_n_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_n_u2080_3321_, lean_object* v_filter_3322_, lean_object* v_view_x3f_3323_, lean_object* v_toBind_3324_, lean_object* v___f_3325_, lean_object* v___f_3326_, lean_object* v___x_3327_, lean_object* v_____do__lift_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3313_, v_n_3314_, v_inst_3315_, v_inst_3316_, v_inst_3317_, v_inst_3318_, v_inst_3319_, v_inst_3320_, v_n_u2080_3321_, v_filter_3322_, v_view_x3f_3323_, v_toBind_3324_, v___f_3325_, v___f_3326_, v___x_3327_, v_____do__lift_3328_);
lean_dec(v_____do__lift_3328_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_n_u2080_3336_, lean_object* v_filter_3337_, lean_object* v_view_x3f_3338_, lean_object* v_n_3339_){
_start:
{
lean_object* v___f_3340_; lean_object* v___f_3341_; lean_object* v___f_3342_; lean_object* v___f_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___y_3351_; uint8_t v___x_3359_; 
lean_inc_ref_n(v_inst_3330_, 7);
v___f_3340_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3340_, 0, v_inst_3330_);
v___f_3341_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3341_, 0, v_inst_3330_);
v___f_3342_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3342_, 0, v_inst_3330_);
v___f_3343_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3343_, 0, v_inst_3330_);
v___f_3344_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3344_, 0, v_inst_3330_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___f_3340_);
lean_ctor_set(v___x_3345_, 1, v___f_3341_);
v___x_3346_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3346_, 0, lean_box(0));
lean_closure_set(v___x_3346_, 1, v_inst_3330_);
v___x_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
lean_ctor_set(v___x_3347_, 2, v___f_3342_);
lean_ctor_set(v___x_3347_, 3, v___f_3343_);
lean_ctor_set(v___x_3347_, 4, v___f_3344_);
v___x_3348_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3348_, 0, lean_box(0));
lean_closure_set(v___x_3348_, 1, v_inst_3330_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3359_ = l_Lean_Name_hasMacroScopes(v_n_3339_);
if (v___x_3359_ == 0)
{
lean_object* v_toApplicative_3360_; lean_object* v_toPure_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_toApplicative_3360_ = lean_ctor_get(v_inst_3330_, 0);
v_toPure_3361_ = lean_ctor_get(v_toApplicative_3360_, 1);
v___x_3362_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3361_);
v___x_3363_ = lean_apply_2(v_toPure_3361_, lean_box(0), v___x_3362_);
v___y_3351_ = v___x_3363_;
goto v___jp_3350_;
}
else
{
lean_object* v_toApplicative_3364_; lean_object* v_toPure_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_toApplicative_3364_ = lean_ctor_get(v_inst_3330_, 0);
v_toPure_3365_ = lean_ctor_get(v_toApplicative_3364_, 1);
v___x_3366_ = lean_box(0);
lean_inc(v_toPure_3365_);
v___x_3367_ = lean_apply_2(v_toPure_3365_, lean_box(0), v___x_3366_);
v___y_3351_ = v___x_3367_;
goto v___jp_3350_;
}
v___jp_3350_:
{
lean_object* v_toApplicative_3352_; lean_object* v_toBind_3353_; lean_object* v_toPure_3354_; lean_object* v___f_3355_; lean_object* v___f_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; 
v_toApplicative_3352_ = lean_ctor_get(v_inst_3330_, 0);
v_toBind_3353_ = lean_ctor_get(v_inst_3330_, 1);
lean_inc_n(v_toBind_3353_, 2);
v_toPure_3354_ = lean_ctor_get(v_toApplicative_3352_, 1);
lean_inc_n(v_toPure_3354_, 3);
v___f_3355_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3355_, 0, v_toPure_3354_);
v___f_3356_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3356_, 0, v_toPure_3354_);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3357_, 0, v_toPure_3354_);
lean_closure_set(v___f_3357_, 1, v_n_3339_);
lean_closure_set(v___f_3357_, 2, v_inst_3330_);
lean_closure_set(v___f_3357_, 3, v_inst_3331_);
lean_closure_set(v___f_3357_, 4, v_inst_3332_);
lean_closure_set(v___f_3357_, 5, v_inst_3333_);
lean_closure_set(v___f_3357_, 6, v_inst_3334_);
lean_closure_set(v___f_3357_, 7, v_inst_3335_);
lean_closure_set(v___f_3357_, 8, v_n_u2080_3336_);
lean_closure_set(v___f_3357_, 9, v_filter_3337_);
lean_closure_set(v___f_3357_, 10, v_view_x3f_3338_);
lean_closure_set(v___f_3357_, 11, v_toBind_3353_);
lean_closure_set(v___f_3357_, 12, v___f_3356_);
lean_closure_set(v___f_3357_, 13, v___f_3355_);
lean_closure_set(v___f_3357_, 14, v___x_3349_);
v___x_3358_ = lean_apply_4(v_toBind_3353_, lean_box(0), lean_box(0), v___y_3351_, v___f_3357_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_inst_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_n_u2080_3375_, lean_object* v_filter_3376_, lean_object* v_view_x3f_3377_, lean_object* v_n_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3369_, v_inst_3370_, v_inst_3371_, v_inst_3372_, v_inst_3373_, v_inst_3374_, v_n_u2080_3375_, v_filter_3376_, v_view_x3f_3377_, v_n_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3380_, lean_object* v_x1_3381_, lean_object* v_x2_3382_){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3383_ = l_Lean_Name_getPrefix(v_x2_3382_);
v___x_3384_ = l_Lean_Name_getPrefix(v_n_u2081_3380_);
v___x_3385_ = l_Lean_Name_isPrefixOf(v___x_3383_, v___x_3384_);
lean_dec(v___x_3384_);
lean_dec(v___x_3383_);
if (v___x_3385_ == 0)
{
lean_dec(v_x2_3382_);
return v_x1_3381_;
}
else
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_array_push(v_x1_3381_, v_x2_3382_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3387_, lean_object* v_x1_3388_, lean_object* v_x2_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3387_, v_x1_3388_, v_x2_3389_);
lean_dec(v_n_u2081_3387_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3391_, lean_object* v_n_u2081_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_inst_3396_, lean_object* v_inst_3397_, lean_object* v_inst_3398_, lean_object* v_n_u2080_3399_, lean_object* v_filter_3400_, lean_object* v_toPure_3401_, lean_object* v_____do__lift_3402_){
_start:
{
if (lean_obj_tag(v_____do__lift_3402_) == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec(v_toPure_3401_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_view_3391_);
v___x_3404_ = l_Lean_rootNamespace;
v___x_3405_ = l_Lean_Name_append(v___x_3404_, v_n_u2081_3392_);
v___x_3406_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3393_, v_inst_3394_, v_inst_3395_, v_inst_3396_, v_inst_3397_, v_inst_3398_, v_n_u2080_3399_, v_filter_3400_, v___x_3403_, v___x_3405_);
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; 
lean_dec(v_filter_3400_);
lean_dec(v_n_u2080_3399_);
lean_dec(v_inst_3398_);
lean_dec_ref(v_inst_3397_);
lean_dec_ref(v_inst_3396_);
lean_dec_ref(v_inst_3395_);
lean_dec_ref(v_inst_3394_);
lean_dec_ref(v_inst_3393_);
lean_dec(v_n_u2081_3392_);
lean_dec_ref(v_view_3391_);
v___x_3407_ = lean_apply_2(v_toPure_3401_, lean_box(0), v_____do__lift_3402_);
return v___x_3407_;
}
}
}
lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3408_, lean_object* v_inst_3409_, lean_object* v_inst_3410_, lean_object* v_inst_3411_, lean_object* v_inst_3412_, lean_object* v_inst_3413_, lean_object* v_inst_3414_, lean_object* v_n_u2080_3415_, lean_object* v_filter_3416_, lean_object* v___x_3417_, lean_object* v_toBind_3418_, lean_object* v___f_3419_, uint8_t v_allowHorizAliases_3420_, lean_object* v___f_3421_, lean_object* v_____do__lift_3422_){
_start:
{
lean_object* v_aliases_3424_; 
if (lean_obj_tag(v_____do__lift_3422_) == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec_ref(v___f_3421_);
lean_dec(v___f_3419_);
lean_dec(v_toBind_3418_);
lean_dec_ref(v___x_3417_);
lean_dec(v_filter_3416_);
lean_dec(v_n_u2080_3415_);
lean_dec(v_inst_3414_);
lean_dec_ref(v_inst_3413_);
lean_dec_ref(v_inst_3412_);
lean_dec_ref(v_inst_3411_);
lean_dec_ref(v_inst_3410_);
lean_dec_ref(v_inst_3409_);
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_apply_2(v_toPure_3408_, lean_box(0), v___x_3430_);
return v___x_3431_;
}
else
{
lean_object* v_val_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_toPure_3408_);
v_val_3432_ = lean_ctor_get(v_____do__lift_3422_, 0);
lean_inc(v_val_3432_);
lean_dec_ref_known(v_____do__lift_3422_, 1);
lean_inc(v_n_u2080_3415_);
v___x_3433_ = l_Lean_getRevAliases(v_val_3432_, v_n_u2080_3415_);
v___x_3434_ = lean_array_mk(v___x_3433_);
if (v_allowHorizAliases_3420_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v___x_3436_ = lean_array_get_size(v___x_3434_);
v___x_3437_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3438_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3439_ = lean_nat_dec_lt(v___x_3435_, v___x_3436_);
if (v___x_3439_ == 0)
{
lean_dec_ref(v___x_3434_);
lean_dec_ref(v___f_3421_);
v_aliases_3424_ = v___x_3437_;
goto v___jp_3423_;
}
else
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_nat_dec_le(v___x_3436_, v___x_3436_);
if (v___x_3440_ == 0)
{
if (v___x_3439_ == 0)
{
lean_dec_ref(v___x_3434_);
lean_dec_ref(v___f_3421_);
v_aliases_3424_ = v___x_3437_;
goto v___jp_3423_;
}
else
{
size_t v___x_3441_; size_t v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = lean_usize_of_nat(v___x_3436_);
v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3438_, v___f_3421_, v___x_3434_, v___x_3441_, v___x_3442_, v___x_3437_);
v_aliases_3424_ = v___x_3443_;
goto v___jp_3423_;
}
}
else
{
size_t v___x_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = ((size_t)0ULL);
v___x_3445_ = lean_usize_of_nat(v___x_3436_);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3438_, v___f_3421_, v___x_3434_, v___x_3444_, v___x_3445_, v___x_3437_);
v_aliases_3424_ = v___x_3446_;
goto v___jp_3423_;
}
}
}
else
{
lean_dec_ref(v___f_3421_);
v_aliases_3424_ = v___x_3434_;
goto v___jp_3423_;
}
}
v___jp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3426_, 0, lean_box(0));
lean_closure_set(v___x_3426_, 1, v_inst_3409_);
lean_closure_set(v___x_3426_, 2, v_inst_3410_);
lean_closure_set(v___x_3426_, 3, v_inst_3411_);
lean_closure_set(v___x_3426_, 4, v_inst_3412_);
lean_closure_set(v___x_3426_, 5, v_inst_3413_);
lean_closure_set(v___x_3426_, 6, v_inst_3414_);
lean_closure_set(v___x_3426_, 7, v_n_u2080_3415_);
lean_closure_set(v___x_3426_, 8, v_filter_3416_);
lean_closure_set(v___x_3426_, 9, v___x_3425_);
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3417_, v___x_3426_, v_aliases_3424_, v___x_3427_);
v___x_3429_ = lean_apply_4(v_toBind_3418_, lean_box(0), lean_box(0), v___x_3428_, v___f_3419_);
return v___x_3429_;
}
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobal_x3f___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3408_ = stack[0].m_obj;
lean_object* v_inst_3409_ = stack[1].m_obj;
lean_object* v_inst_3410_ = stack[2].m_obj;
lean_object* v_inst_3411_ = stack[3].m_obj;
lean_object* v_inst_3412_ = stack[4].m_obj;
lean_object* v_inst_3413_ = stack[5].m_obj;
lean_object* v_inst_3414_ = stack[6].m_obj;
lean_object* v_n_u2080_3415_ = stack[7].m_obj;
lean_object* v_filter_3416_ = stack[8].m_obj;
lean_object* v___x_3417_ = stack[9].m_obj;
lean_object* v_toBind_3418_ = stack[10].m_obj;
lean_object* v___f_3419_ = stack[11].m_obj;
uint8_t v_allowHorizAliases_3420_ = stack[12].m_num;
lean_object* v___f_3421_ = stack[13].m_obj;
lean_object* v_____do__lift_3422_ = stack[14].m_obj;
lean_object* v_res_3447_;
v_res_3447_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3408_, v_inst_3409_, v_inst_3410_, v_inst_3411_, v_inst_3412_, v_inst_3413_, v_inst_3414_, v_n_u2080_3415_, v_filter_3416_, v___x_3417_, v_toBind_3418_, v___f_3419_, v_allowHorizAliases_3420_, v___f_3421_, v_____do__lift_3422_);
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_n_u2080_3455_, lean_object* v_filter_3456_, lean_object* v___x_3457_, lean_object* v_toBind_3458_, lean_object* v___f_3459_, lean_object* v_allowHorizAliases_3460_, lean_object* v___f_3461_, lean_object* v_____do__lift_3462_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3463_; lean_object* v_res_3464_; 
v_allowHorizAliases_boxed_3463_ = lean_unbox(v_allowHorizAliases_3460_);
v_res_3464_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3448_, v_inst_3449_, v_inst_3450_, v_inst_3451_, v_inst_3452_, v_inst_3453_, v_inst_3454_, v_n_u2080_3455_, v_filter_3456_, v___x_3457_, v_toBind_3458_, v___f_3459_, v_allowHorizAliases_boxed_3463_, v___f_3461_, v_____do__lift_3462_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3465_, lean_object* v_____do__lift_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_____do__lift_3466_);
v___x_3468_ = lean_apply_2(v_toPure_3465_, lean_box(0), v___x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_inst_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_n_u2080_3476_, lean_object* v_filter_3477_, lean_object* v___x_3478_, lean_object* v_toPure_3479_, lean_object* v_____do__lift_3480_){
_start:
{
if (lean_obj_tag(v_____do__lift_3480_) == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v_toPure_3479_);
v___x_3481_ = l_Lean_rootNamespace;
v___x_3482_ = l_Lean_Name_append(v___x_3481_, v_n_u2081_3469_);
v___x_3483_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3470_, v_inst_3471_, v_inst_3472_, v_inst_3473_, v_inst_3474_, v_inst_3475_, v_n_u2080_3476_, v_filter_3477_, v___x_3478_, v___x_3482_);
return v___x_3483_;
}
else
{
lean_object* v___x_3484_; 
lean_dec(v___x_3478_);
lean_dec(v_filter_3477_);
lean_dec(v_n_u2080_3476_);
lean_dec(v_inst_3475_);
lean_dec_ref(v_inst_3474_);
lean_dec_ref(v_inst_3473_);
lean_dec_ref(v_inst_3472_);
lean_dec_ref(v_inst_3471_);
lean_dec_ref(v_inst_3470_);
lean_dec(v_n_u2081_3469_);
v___x_3484_ = lean_apply_2(v_toPure_3479_, lean_box(0), v_____do__lift_3480_);
return v___x_3484_;
}
}
}
lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3485_, lean_object* v_inst_3486_, lean_object* v_inst_3487_, lean_object* v_inst_3488_, lean_object* v_inst_3489_, lean_object* v_inst_3490_, lean_object* v_n_u2080_3491_, uint8_t v_fullNames_3492_, uint8_t v_allowHorizAliases_3493_, lean_object* v_filter_3494_){
_start:
{
lean_object* v_view_3495_; lean_object* v_name_3496_; lean_object* v_n_u2081_3497_; lean_object* v___x_3498_; 
lean_inc(v_n_u2080_3491_);
v_view_3495_ = l_Lean_extractMacroScopes(v_n_u2080_3491_);
v_name_3496_ = lean_ctor_get(v_view_3495_, 0);
lean_inc(v_name_3496_);
v_n_u2081_3497_ = l_Lean_privateToUserName(v_name_3496_);
lean_inc_ref(v_inst_3485_);
v___x_3498_ = l_OptionT_instAlternative___redArg(v_inst_3485_);
if (v_fullNames_3492_ == 0)
{
lean_object* v_toApplicative_3499_; lean_object* v_getEnv_3500_; lean_object* v_toBind_3501_; lean_object* v_toPure_3502_; lean_object* v___f_3503_; lean_object* v___f_3504_; lean_object* v___x_3505_; lean_object* v___f_3506_; lean_object* v___f_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_toApplicative_3499_ = lean_ctor_get(v_inst_3485_, 0);
v_getEnv_3500_ = lean_ctor_get(v_inst_3487_, 0);
lean_inc(v_getEnv_3500_);
v_toBind_3501_ = lean_ctor_get(v_inst_3485_, 1);
lean_inc_n(v_toBind_3501_, 3);
v_toPure_3502_ = lean_ctor_get(v_toApplicative_3499_, 1);
lean_inc_n(v_toPure_3502_, 3);
lean_inc(v_n_u2081_3497_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3503_, 0, v_n_u2081_3497_);
lean_inc(v_filter_3494_);
lean_inc(v_n_u2080_3491_);
lean_inc(v_inst_3490_);
lean_inc_ref(v_inst_3489_);
lean_inc_ref(v_inst_3488_);
lean_inc_ref(v_inst_3487_);
lean_inc_ref(v_inst_3486_);
lean_inc_ref(v_inst_3485_);
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3504_, 0, v_view_3495_);
lean_closure_set(v___f_3504_, 1, v_n_u2081_3497_);
lean_closure_set(v___f_3504_, 2, v_inst_3485_);
lean_closure_set(v___f_3504_, 3, v_inst_3486_);
lean_closure_set(v___f_3504_, 4, v_inst_3487_);
lean_closure_set(v___f_3504_, 5, v_inst_3488_);
lean_closure_set(v___f_3504_, 6, v_inst_3489_);
lean_closure_set(v___f_3504_, 7, v_inst_3490_);
lean_closure_set(v___f_3504_, 8, v_n_u2080_3491_);
lean_closure_set(v___f_3504_, 9, v_filter_3494_);
lean_closure_set(v___f_3504_, 10, v_toPure_3502_);
v___x_3505_ = lean_box(v_allowHorizAliases_3493_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_3506_, 0, v_toPure_3502_);
lean_closure_set(v___f_3506_, 1, v_inst_3485_);
lean_closure_set(v___f_3506_, 2, v_inst_3486_);
lean_closure_set(v___f_3506_, 3, v_inst_3487_);
lean_closure_set(v___f_3506_, 4, v_inst_3488_);
lean_closure_set(v___f_3506_, 5, v_inst_3489_);
lean_closure_set(v___f_3506_, 6, v_inst_3490_);
lean_closure_set(v___f_3506_, 7, v_n_u2080_3491_);
lean_closure_set(v___f_3506_, 8, v_filter_3494_);
lean_closure_set(v___f_3506_, 9, v___x_3498_);
lean_closure_set(v___f_3506_, 10, v_toBind_3501_);
lean_closure_set(v___f_3506_, 11, v___f_3504_);
lean_closure_set(v___f_3506_, 12, v___x_3505_);
lean_closure_set(v___f_3506_, 13, v___f_3503_);
v___f_3507_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3507_, 0, v_toPure_3502_);
v___x_3508_ = lean_apply_4(v_toBind_3501_, lean_box(0), lean_box(0), v_getEnv_3500_, v___f_3507_);
v___x_3509_ = lean_apply_4(v_toBind_3501_, lean_box(0), lean_box(0), v___x_3508_, v___f_3506_);
return v___x_3509_;
}
else
{
lean_object* v_toApplicative_3510_; lean_object* v_toBind_3511_; lean_object* v_toPure_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; 
lean_dec_ref(v___x_3498_);
v_toApplicative_3510_ = lean_ctor_get(v_inst_3485_, 0);
v_toBind_3511_ = lean_ctor_get(v_inst_3485_, 1);
lean_inc(v_toBind_3511_);
v_toPure_3512_ = lean_ctor_get(v_toApplicative_3510_, 1);
lean_inc(v_toPure_3512_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_view_3495_);
lean_inc(v_n_u2081_3497_);
lean_inc_ref(v___x_3513_);
lean_inc(v_filter_3494_);
lean_inc(v_n_u2080_3491_);
lean_inc(v_inst_3490_);
lean_inc_ref(v_inst_3489_);
lean_inc_ref(v_inst_3488_);
lean_inc_ref(v_inst_3487_);
lean_inc_ref(v_inst_3486_);
lean_inc_ref(v_inst_3485_);
v___x_3514_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3485_, v_inst_3486_, v_inst_3487_, v_inst_3488_, v_inst_3489_, v_inst_3490_, v_n_u2080_3491_, v_filter_3494_, v___x_3513_, v_n_u2081_3497_);
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3515_, 0, v_n_u2081_3497_);
lean_closure_set(v___f_3515_, 1, v_inst_3485_);
lean_closure_set(v___f_3515_, 2, v_inst_3486_);
lean_closure_set(v___f_3515_, 3, v_inst_3487_);
lean_closure_set(v___f_3515_, 4, v_inst_3488_);
lean_closure_set(v___f_3515_, 5, v_inst_3489_);
lean_closure_set(v___f_3515_, 6, v_inst_3490_);
lean_closure_set(v___f_3515_, 7, v_n_u2080_3491_);
lean_closure_set(v___f_3515_, 8, v_filter_3494_);
lean_closure_set(v___f_3515_, 9, v___x_3513_);
lean_closure_set(v___f_3515_, 10, v_toPure_3512_);
v___x_3516_ = lean_apply_4(v_toBind_3511_, lean_box(0), lean_box(0), v___x_3514_, v___f_3515_);
return v___x_3516_;
}
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobal_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3485_ = stack[0].m_obj;
lean_object* v_inst_3486_ = stack[1].m_obj;
lean_object* v_inst_3487_ = stack[2].m_obj;
lean_object* v_inst_3488_ = stack[3].m_obj;
lean_object* v_inst_3489_ = stack[4].m_obj;
lean_object* v_inst_3490_ = stack[5].m_obj;
lean_object* v_n_u2080_3491_ = stack[6].m_obj;
uint8_t v_fullNames_3492_ = stack[7].m_num;
uint8_t v_allowHorizAliases_3493_ = stack[8].m_num;
lean_object* v_filter_3494_ = stack[9].m_obj;
lean_object* v_res_3517_;
v_res_3517_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3485_, v_inst_3486_, v_inst_3487_, v_inst_3488_, v_inst_3489_, v_inst_3490_, v_n_u2080_3491_, v_fullNames_3492_, v_allowHorizAliases_3493_, v_filter_3494_);
stack->m_obj
 = v_res_3517_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3518_, lean_object* v_inst_3519_, lean_object* v_inst_3520_, lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_n_u2080_3524_, lean_object* v_fullNames_3525_, lean_object* v_allowHorizAliases_3526_, lean_object* v_filter_3527_){
_start:
{
uint8_t v_fullNames_boxed_3528_; uint8_t v_allowHorizAliases_boxed_3529_; lean_object* v_res_3530_; 
v_fullNames_boxed_3528_ = lean_unbox(v_fullNames_3525_);
v_allowHorizAliases_boxed_3529_ = lean_unbox(v_allowHorizAliases_3526_);
v_res_3530_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3518_, v_inst_3519_, v_inst_3520_, v_inst_3521_, v_inst_3522_, v_inst_3523_, v_n_u2080_3524_, v_fullNames_boxed_3528_, v_allowHorizAliases_boxed_3529_, v_filter_3527_);
return v_res_3530_;
}
}
lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_inst_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_n_u2080_3538_, uint8_t v_fullNames_3539_, uint8_t v_allowHorizAliases_3540_, lean_object* v_filter_3541_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3532_, v_inst_3533_, v_inst_3534_, v_inst_3535_, v_inst_3536_, v_inst_3537_, v_n_u2080_3538_, v_fullNames_3539_, v_allowHorizAliases_3540_, v_filter_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobal_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3532_ = stack[1].m_obj;
lean_object* v_inst_3533_ = stack[2].m_obj;
lean_object* v_inst_3534_ = stack[3].m_obj;
lean_object* v_inst_3535_ = stack[4].m_obj;
lean_object* v_inst_3536_ = stack[5].m_obj;
lean_object* v_inst_3537_ = stack[6].m_obj;
lean_object* v_n_u2080_3538_ = stack[7].m_obj;
uint8_t v_fullNames_3539_ = stack[8].m_num;
uint8_t v_allowHorizAliases_3540_ = stack[9].m_num;
lean_object* v_filter_3541_ = stack[10].m_obj;
lean_object* v_res_3543_;
v_res_3543_ = l_Lean_unresolveNameGlobal_x3f(lean_box(0), v_inst_3532_, v_inst_3533_, v_inst_3534_, v_inst_3535_, v_inst_3536_, v_inst_3537_, v_n_u2080_3538_, v_fullNames_3539_, v_allowHorizAliases_3540_, v_filter_3541_);
stack->m_obj
 = v_res_3543_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3544_, lean_object* v_inst_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_n_u2080_3551_, lean_object* v_fullNames_3552_, lean_object* v_allowHorizAliases_3553_, lean_object* v_filter_3554_){
_start:
{
uint8_t v_fullNames_boxed_3555_; uint8_t v_allowHorizAliases_boxed_3556_; lean_object* v_res_3557_; 
v_fullNames_boxed_3555_ = lean_unbox(v_fullNames_3552_);
v_allowHorizAliases_boxed_3556_ = lean_unbox(v_allowHorizAliases_3553_);
v_res_3557_ = l_Lean_unresolveNameGlobal_x3f(v_m_3544_, v_inst_3545_, v_inst_3546_, v_inst_3547_, v_inst_3548_, v_inst_3549_, v_inst_3550_, v_n_u2080_3551_, v_fullNames_boxed_3555_, v_allowHorizAliases_boxed_3556_, v_filter_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3558_, lean_object* v_n_u2080_3559_, lean_object* v_n_x3f_3560_){
_start:
{
if (lean_obj_tag(v_n_x3f_3560_) == 0)
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_apply_2(v_toPure_3558_, lean_box(0), v_n_u2080_3559_);
return v___x_3561_;
}
else
{
lean_object* v_val_3562_; lean_object* v___x_3563_; 
lean_dec(v_n_u2080_3559_);
v_val_3562_ = lean_ctor_get(v_n_x3f_3560_, 0);
lean_inc(v_val_3562_);
lean_dec_ref_known(v_n_x3f_3560_, 1);
v___x_3563_ = lean_apply_2(v_toPure_3558_, lean_box(0), v_val_3562_);
return v___x_3563_;
}
}
}
lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_n_u2080_3570_, uint8_t v_fullNames_3571_, uint8_t v_allowHorizAliases_3572_, lean_object* v_filter_3573_){
_start:
{
lean_object* v_toApplicative_3574_; lean_object* v_toBind_3575_; lean_object* v_toPure_3576_; lean_object* v___x_3577_; lean_object* v___f_3578_; lean_object* v___x_3579_; 
v_toApplicative_3574_ = lean_ctor_get(v_inst_3564_, 0);
v_toBind_3575_ = lean_ctor_get(v_inst_3564_, 1);
lean_inc(v_toBind_3575_);
v_toPure_3576_ = lean_ctor_get(v_toApplicative_3574_, 1);
lean_inc(v_toPure_3576_);
lean_inc(v_n_u2080_3570_);
v___x_3577_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3564_, v_inst_3565_, v_inst_3566_, v_inst_3567_, v_inst_3568_, v_inst_3569_, v_n_u2080_3570_, v_fullNames_3571_, v_allowHorizAliases_3572_, v_filter_3573_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3578_, 0, v_toPure_3576_);
lean_closure_set(v___f_3578_, 1, v_n_u2080_3570_);
v___x_3579_ = lean_apply_4(v_toBind_3575_, lean_box(0), lean_box(0), v___x_3577_, v___f_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3564_ = stack[0].m_obj;
lean_object* v_inst_3565_ = stack[1].m_obj;
lean_object* v_inst_3566_ = stack[2].m_obj;
lean_object* v_inst_3567_ = stack[3].m_obj;
lean_object* v_inst_3568_ = stack[4].m_obj;
lean_object* v_inst_3569_ = stack[5].m_obj;
lean_object* v_n_u2080_3570_ = stack[6].m_obj;
uint8_t v_fullNames_3571_ = stack[7].m_num;
uint8_t v_allowHorizAliases_3572_ = stack[8].m_num;
lean_object* v_filter_3573_ = stack[9].m_obj;
lean_object* v_res_3580_;
v_res_3580_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3564_, v_inst_3565_, v_inst_3566_, v_inst_3567_, v_inst_3568_, v_inst_3569_, v_n_u2080_3570_, v_fullNames_3571_, v_allowHorizAliases_3572_, v_filter_3573_);
stack->m_obj
 = v_res_3580_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_n_u2080_3587_, lean_object* v_fullNames_3588_, lean_object* v_allowHorizAliases_3589_, lean_object* v_filter_3590_){
_start:
{
uint8_t v_fullNames_boxed_3591_; uint8_t v_allowHorizAliases_boxed_3592_; lean_object* v_res_3593_; 
v_fullNames_boxed_3591_ = lean_unbox(v_fullNames_3588_);
v_allowHorizAliases_boxed_3592_ = lean_unbox(v_allowHorizAliases_3589_);
v_res_3593_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3581_, v_inst_3582_, v_inst_3583_, v_inst_3584_, v_inst_3585_, v_inst_3586_, v_n_u2080_3587_, v_fullNames_boxed_3591_, v_allowHorizAliases_boxed_3592_, v_filter_3590_);
return v_res_3593_;
}
}
lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3594_, lean_object* v_inst_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_n_u2080_3601_, uint8_t v_fullNames_3602_, uint8_t v_allowHorizAliases_3603_, lean_object* v_filter_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3595_, v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_n_u2080_3601_, v_fullNames_3602_, v_allowHorizAliases_3603_, v_filter_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobal_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3595_ = stack[1].m_obj;
lean_object* v_inst_3596_ = stack[2].m_obj;
lean_object* v_inst_3597_ = stack[3].m_obj;
lean_object* v_inst_3598_ = stack[4].m_obj;
lean_object* v_inst_3599_ = stack[5].m_obj;
lean_object* v_inst_3600_ = stack[6].m_obj;
lean_object* v_n_u2080_3601_ = stack[7].m_obj;
uint8_t v_fullNames_3602_ = stack[8].m_num;
uint8_t v_allowHorizAliases_3603_ = stack[9].m_num;
lean_object* v_filter_3604_ = stack[10].m_obj;
lean_object* v_res_3606_;
v_res_3606_ = l_Lean_unresolveNameGlobal(lean_box(0), v_inst_3595_, v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_n_u2080_3601_, v_fullNames_3602_, v_allowHorizAliases_3603_, v_filter_3604_);
stack->m_obj
 = v_res_3606_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3607_, lean_object* v_inst_3608_, lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_n_u2080_3614_, lean_object* v_fullNames_3615_, lean_object* v_allowHorizAliases_3616_, lean_object* v_filter_3617_){
_start:
{
uint8_t v_fullNames_boxed_3618_; uint8_t v_allowHorizAliases_boxed_3619_; lean_object* v_res_3620_; 
v_fullNames_boxed_3618_ = lean_unbox(v_fullNames_3615_);
v_allowHorizAliases_boxed_3619_ = lean_unbox(v_allowHorizAliases_3616_);
v_res_3620_ = l_Lean_unresolveNameGlobal(v_m_3607_, v_inst_3608_, v_inst_3609_, v_inst_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_, v_n_u2080_3614_, v_fullNames_boxed_3618_, v_allowHorizAliases_boxed_3619_, v_filter_3617_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3622_, lean_object* v_inst_3623_, lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_n_3630_){
_start:
{
lean_object* v_map_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_map_3631_ = lean_ctor_get(v_toFunctor_3622_, 0);
lean_inc(v_map_3631_);
lean_dec_ref(v_toFunctor_3622_);
v___x_3632_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3633_ = l_Lean_resolveLocalName___redArg(v_inst_3623_, v_inst_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_n_3630_);
v___x_3634_ = lean_apply_4(v_map_3631_, lean_box(0), lean_box(0), v___x_3632_, v___x_3633_);
return v___x_3634_;
}
}
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_n_u2080_3642_, uint8_t v_fullNames_3643_){
_start:
{
lean_object* v_toApplicative_3644_; lean_object* v_toFunctor_3645_; uint8_t v___x_3646_; lean_object* v___f_3647_; lean_object* v___x_3648_; 
v_toApplicative_3644_ = lean_ctor_get(v_inst_3635_, 0);
v_toFunctor_3645_ = lean_ctor_get(v_toApplicative_3644_, 0);
v___x_3646_ = 0;
lean_inc(v_inst_3640_);
lean_inc_ref(v_inst_3639_);
lean_inc_ref(v_inst_3638_);
lean_inc_ref(v_inst_3637_);
lean_inc_ref(v_inst_3636_);
lean_inc_ref(v_inst_3635_);
lean_inc_ref(v_toFunctor_3645_);
v___f_3647_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3647_, 0, v_toFunctor_3645_);
lean_closure_set(v___f_3647_, 1, v_inst_3635_);
lean_closure_set(v___f_3647_, 2, v_inst_3636_);
lean_closure_set(v___f_3647_, 3, v_inst_3637_);
lean_closure_set(v___f_3647_, 4, v_inst_3638_);
lean_closure_set(v___f_3647_, 5, v_inst_3639_);
lean_closure_set(v___f_3647_, 6, v_inst_3640_);
lean_closure_set(v___f_3647_, 7, v_inst_3641_);
v___x_3648_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3635_, v_inst_3636_, v_inst_3637_, v_inst_3638_, v_inst_3639_, v_inst_3640_, v_n_u2080_3642_, v_fullNames_3643_, v___x_3646_, v___f_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3635_ = stack[0].m_obj;
lean_object* v_inst_3636_ = stack[1].m_obj;
lean_object* v_inst_3637_ = stack[2].m_obj;
lean_object* v_inst_3638_ = stack[3].m_obj;
lean_object* v_inst_3639_ = stack[4].m_obj;
lean_object* v_inst_3640_ = stack[5].m_obj;
lean_object* v_inst_3641_ = stack[6].m_obj;
lean_object* v_n_u2080_3642_ = stack[7].m_obj;
uint8_t v_fullNames_3643_ = stack[8].m_num;
lean_object* v_res_3649_;
v_res_3649_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3635_, v_inst_3636_, v_inst_3637_, v_inst_3638_, v_inst_3639_, v_inst_3640_, v_inst_3641_, v_n_u2080_3642_, v_fullNames_3643_);
stack->m_obj
 = v_res_3649_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3650_, lean_object* v_inst_3651_, lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_inst_3654_, lean_object* v_inst_3655_, lean_object* v_inst_3656_, lean_object* v_n_u2080_3657_, lean_object* v_fullNames_3658_){
_start:
{
uint8_t v_fullNames_boxed_3659_; lean_object* v_res_3660_; 
v_fullNames_boxed_3659_ = lean_unbox(v_fullNames_3658_);
v_res_3660_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3650_, v_inst_3651_, v_inst_3652_, v_inst_3653_, v_inst_3654_, v_inst_3655_, v_inst_3656_, v_n_u2080_3657_, v_fullNames_boxed_3659_);
return v_res_3660_;
}
}
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_inst_3666_, lean_object* v_inst_3667_, lean_object* v_inst_3668_, lean_object* v_n_u2080_3669_, uint8_t v_fullNames_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3662_, v_inst_3663_, v_inst_3664_, v_inst_3665_, v_inst_3666_, v_inst_3667_, v_inst_3668_, v_n_u2080_3669_, v_fullNames_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobalAvoidingLocals_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3662_ = stack[1].m_obj;
lean_object* v_inst_3663_ = stack[2].m_obj;
lean_object* v_inst_3664_ = stack[3].m_obj;
lean_object* v_inst_3665_ = stack[4].m_obj;
lean_object* v_inst_3666_ = stack[5].m_obj;
lean_object* v_inst_3667_ = stack[6].m_obj;
lean_object* v_inst_3668_ = stack[7].m_obj;
lean_object* v_n_u2080_3669_ = stack[8].m_obj;
uint8_t v_fullNames_3670_ = stack[9].m_num;
lean_object* v_res_3672_;
v_res_3672_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_box(0), v_inst_3662_, v_inst_3663_, v_inst_3664_, v_inst_3665_, v_inst_3666_, v_inst_3667_, v_inst_3668_, v_n_u2080_3669_, v_fullNames_3670_);
stack->m_obj
 = v_res_3672_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3673_, lean_object* v_inst_3674_, lean_object* v_inst_3675_, lean_object* v_inst_3676_, lean_object* v_inst_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_n_u2080_3681_, lean_object* v_fullNames_3682_){
_start:
{
uint8_t v_fullNames_boxed_3683_; lean_object* v_res_3684_; 
v_fullNames_boxed_3683_ = lean_unbox(v_fullNames_3682_);
v_res_3684_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3673_, v_inst_3674_, v_inst_3675_, v_inst_3676_, v_inst_3677_, v_inst_3678_, v_inst_3679_, v_inst_3680_, v_n_u2080_3681_, v_fullNames_boxed_3683_);
return v_res_3684_;
}
}
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_inst_3687_, lean_object* v_inst_3688_, lean_object* v_inst_3689_, lean_object* v_inst_3690_, lean_object* v_inst_3691_, lean_object* v_n_u2080_3692_, uint8_t v_fullNames_3693_){
_start:
{
lean_object* v_toApplicative_3694_; lean_object* v_toBind_3695_; lean_object* v_toPure_3696_; lean_object* v___x_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; 
v_toApplicative_3694_ = lean_ctor_get(v_inst_3685_, 0);
v_toBind_3695_ = lean_ctor_get(v_inst_3685_, 1);
lean_inc(v_toBind_3695_);
v_toPure_3696_ = lean_ctor_get(v_toApplicative_3694_, 1);
lean_inc(v_toPure_3696_);
lean_inc(v_n_u2080_3692_);
v___x_3697_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3685_, v_inst_3686_, v_inst_3687_, v_inst_3688_, v_inst_3689_, v_inst_3690_, v_inst_3691_, v_n_u2080_3692_, v_fullNames_3693_);
v___f_3698_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3698_, 0, v_toPure_3696_);
lean_closure_set(v___f_3698_, 1, v_n_u2080_3692_);
v___x_3699_ = lean_apply_4(v_toBind_3695_, lean_box(0), lean_box(0), v___x_3697_, v___f_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobalAvoidingLocals___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3685_ = stack[0].m_obj;
lean_object* v_inst_3686_ = stack[1].m_obj;
lean_object* v_inst_3687_ = stack[2].m_obj;
lean_object* v_inst_3688_ = stack[3].m_obj;
lean_object* v_inst_3689_ = stack[4].m_obj;
lean_object* v_inst_3690_ = stack[5].m_obj;
lean_object* v_inst_3691_ = stack[6].m_obj;
lean_object* v_n_u2080_3692_ = stack[7].m_obj;
uint8_t v_fullNames_3693_ = stack[8].m_num;
lean_object* v_res_3700_;
v_res_3700_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3685_, v_inst_3686_, v_inst_3687_, v_inst_3688_, v_inst_3689_, v_inst_3690_, v_inst_3691_, v_n_u2080_3692_, v_fullNames_3693_);
stack->m_obj
 = v_res_3700_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_inst_3707_, lean_object* v_n_u2080_3708_, lean_object* v_fullNames_3709_){
_start:
{
uint8_t v_fullNames_boxed_3710_; lean_object* v_res_3711_; 
v_fullNames_boxed_3710_ = lean_unbox(v_fullNames_3709_);
v_res_3711_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3701_, v_inst_3702_, v_inst_3703_, v_inst_3704_, v_inst_3705_, v_inst_3706_, v_inst_3707_, v_n_u2080_3708_, v_fullNames_boxed_3710_);
return v_res_3711_;
}
}
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_inst_3717_, lean_object* v_inst_3718_, lean_object* v_inst_3719_, lean_object* v_n_u2080_3720_, uint8_t v_fullNames_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3713_, v_inst_3714_, v_inst_3715_, v_inst_3716_, v_inst_3717_, v_inst_3718_, v_inst_3719_, v_n_u2080_3720_, v_fullNames_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT void l_Lean_unresolveNameGlobalAvoidingLocals_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3713_ = stack[1].m_obj;
lean_object* v_inst_3714_ = stack[2].m_obj;
lean_object* v_inst_3715_ = stack[3].m_obj;
lean_object* v_inst_3716_ = stack[4].m_obj;
lean_object* v_inst_3717_ = stack[5].m_obj;
lean_object* v_inst_3718_ = stack[6].m_obj;
lean_object* v_inst_3719_ = stack[7].m_obj;
lean_object* v_n_u2080_3720_ = stack[8].m_obj;
uint8_t v_fullNames_3721_ = stack[9].m_num;
lean_object* v_res_3723_;
v_res_3723_ = l_Lean_unresolveNameGlobalAvoidingLocals(lean_box(0), v_inst_3713_, v_inst_3714_, v_inst_3715_, v_inst_3716_, v_inst_3717_, v_inst_3718_, v_inst_3719_, v_n_u2080_3720_, v_fullNames_3721_);
stack->m_obj
 = v_res_3723_;
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3724_, lean_object* v_inst_3725_, lean_object* v_inst_3726_, lean_object* v_inst_3727_, lean_object* v_inst_3728_, lean_object* v_inst_3729_, lean_object* v_inst_3730_, lean_object* v_inst_3731_, lean_object* v_n_u2080_3732_, lean_object* v_fullNames_3733_){
_start:
{
uint8_t v_fullNames_boxed_3734_; lean_object* v_res_3735_; 
v_fullNames_boxed_3734_ = lean_unbox(v_fullNames_3733_);
v_res_3735_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3724_, v_inst_3725_, v_inst_3726_, v_inst_3727_, v_inst_3728_, v_inst_3729_, v_inst_3730_, v_inst_3731_, v_n_u2080_3732_, v_fullNames_boxed_3734_);
return v_res_3735_;
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
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
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
