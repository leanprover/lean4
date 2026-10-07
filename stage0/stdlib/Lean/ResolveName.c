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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(lean_object* v___x_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_st_ref_get(v___x_86_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object* v___x_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(v___x_90_);
lean_dec(v___x_90_);
return v_res_92_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_93_; lean_object* v___f_94_; 
v___x_93_ = l_Lean_reservedNamePredicatesRef;
v___f_94_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_94_, 0, v___x_93_);
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; 
v___f_101_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_box(2);
v___x_104_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_));
v___x_105_ = 0;
v___x_106_ = 1;
v___x_107_ = l_Lean_registerEnvExtension___redArg(v___f_101_, v___x_102_, v___x_103_, v___x_104_, v___x_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
return v_res_109_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_env_110_, lean_object* v_name_111_, lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_154__overap_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_154__overap_116_ = lean_array_uget_borrowed(v_as_112_, v_i_113_);
lean_inc(v___x_154__overap_116_);
lean_inc(v_name_111_);
lean_inc_ref(v_env_110_);
v___x_117_ = lean_apply_2(v___x_154__overap_116_, v_env_110_, v_name_111_);
v___x_118_ = lean_unbox(v___x_117_);
if (v___x_118_ == 0)
{
size_t v___x_119_; size_t v___x_120_; 
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_add(v_i_113_, v___x_119_);
v_i_113_ = v___x_120_;
goto _start;
}
else
{
uint8_t v___x_122_; 
lean_dec(v_name_111_);
lean_dec_ref(v_env_110_);
v___x_122_ = lean_unbox(v___x_117_);
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
lean_dec(v_name_111_);
lean_dec_ref(v_env_110_);
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_env_124_, lean_object* v_name_125_, lean_object* v_as_126_, lean_object* v_i_127_, lean_object* v_stop_128_){
_start:
{
size_t v_i_boxed_129_; size_t v_stop_boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_i_boxed_129_ = lean_unbox_usize(v_i_127_);
lean_dec(v_i_127_);
v_stop_boxed_130_ = lean_unbox_usize(v_stop_128_);
lean_dec(v_stop_128_);
v_res_131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_124_, v_name_125_, v_as_126_, v_i_boxed_129_, v_stop_boxed_130_);
lean_dec_ref(v_as_126_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0(void){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Array_instInhabited___redArg();
return v___x_133_;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* v_env_134_, lean_object* v_name_135_){
_start:
{
lean_object* v___x_136_; lean_object* v_asyncMode_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_136_ = l_Lean_reservedNamePredicatesExt;
v_asyncMode_137_ = lean_ctor_get(v___x_136_, 2);
v___x_138_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_139_ = lean_box(0);
v___x_140_ = 0;
lean_inc_ref(v_env_134_);
v___x_141_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_138_, v___x_136_, v_env_134_, v_asyncMode_137_, v___x_139_, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v___x_141_);
v___x_144_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec(v___x_141_);
lean_dec(v_name_135_);
lean_dec_ref(v_env_134_);
return v___x_144_;
}
else
{
if (v___x_144_ == 0)
{
lean_dec(v___x_141_);
lean_dec(v_name_135_);
lean_dec_ref(v_env_134_);
return v___x_144_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_143_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_134_, v_name_135_, v___x_141_, v___x_145_, v___x_146_);
lean_dec(v___x_141_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_148_, lean_object* v_name_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = lean_is_reserved_name(v_env_148_, v_name_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_ks_156_; lean_object* v_vs_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_181_; 
v_ks_156_ = lean_ctor_get(v_x_152_, 0);
v_vs_157_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_181_ == 0)
{
v___x_159_ = v_x_152_;
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_vs_157_);
lean_inc(v_ks_156_);
lean_dec(v_x_152_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_array_get_size(v_ks_156_);
v___x_162_ = lean_nat_dec_lt(v_x_153_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_x_153_);
v___x_163_ = lean_array_push(v_ks_156_, v_x_154_);
v___x_164_ = lean_array_push(v_vs_157_, v_x_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_164_);
lean_ctor_set(v___x_159_, 0, v___x_163_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_object* v_k_x27_168_; uint8_t v___x_169_; 
v_k_x27_168_ = lean_array_fget_borrowed(v_ks_156_, v_x_153_);
v___x_169_ = lean_name_eq(v_x_154_, v_k_x27_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_171_; 
if (v_isShared_160_ == 0)
{
v___x_171_ = v___x_159_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_ks_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_vs_157_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_add(v_x_153_, v___x_172_);
lean_dec(v_x_153_);
v_x_152_ = v___x_171_;
v_x_153_ = v___x_173_;
goto _start;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = lean_array_fset(v_ks_156_, v_x_153_, v_x_154_);
v___x_177_ = lean_array_fset(v_vs_157_, v_x_153_, v_x_155_);
lean_dec(v_x_153_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_177_);
lean_ctor_set(v___x_159_, 0, v___x_176_);
v___x_179_ = v___x_159_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_182_, lean_object* v_k_183_, lean_object* v_v_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_182_, v___x_185_, v_k_183_, v_v_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_188_, size_t v_x_189_, size_t v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_es_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v_j_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_es_193_ = lean_ctor_get(v_x_188_, 0);
v___x_194_ = ((size_t)31ULL);
v___x_195_ = lean_usize_land(v_x_189_, v___x_194_);
v_j_196_ = lean_usize_to_nat(v___x_195_);
v___x_197_ = lean_array_get_size(v_es_193_);
v___x_198_ = lean_nat_dec_lt(v_j_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_dec(v_j_196_);
lean_dec(v_x_192_);
lean_dec(v_x_191_);
return v_x_188_;
}
else
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_237_; 
lean_inc_ref(v_es_193_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_x_188_, 0);
lean_dec(v_unused_238_);
v___x_200_ = v_x_188_;
v_isShared_201_ = v_isSharedCheck_237_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_x_188_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_237_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_v_202_; lean_object* v___x_203_; lean_object* v_xs_x27_204_; lean_object* v___y_206_; 
v_v_202_ = lean_array_fget(v_es_193_, v_j_196_);
v___x_203_ = lean_box(0);
v_xs_x27_204_ = lean_array_fset(v_es_193_, v_j_196_, v___x_203_);
switch(lean_obj_tag(v_v_202_))
{
case 0:
{
lean_object* v_key_211_; lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_222_; 
v_key_211_ = lean_ctor_get(v_v_202_, 0);
v_val_212_ = lean_ctor_get(v_v_202_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_v_202_);
if (v_isSharedCheck_222_ == 0)
{
v___x_214_ = v_v_202_;
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_inc(v_key_211_);
lean_dec(v_v_202_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
uint8_t v___x_216_; 
v___x_216_ = lean_name_eq(v_x_191_, v_key_211_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_del_object(v___x_214_);
v___x_217_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_211_, v_val_212_, v_x_191_, v_x_192_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
v___y_206_ = v___x_218_;
goto v___jp_205_;
}
else
{
lean_object* v___x_220_; 
lean_dec(v_val_212_);
lean_dec(v_key_211_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v_x_192_);
lean_ctor_set(v___x_214_, 0, v_x_191_);
v___x_220_ = v___x_214_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_x_191_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_x_192_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
v___y_206_ = v___x_220_;
goto v___jp_205_;
}
}
}
}
case 1:
{
lean_object* v_node_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_235_; 
v_node_223_ = lean_ctor_get(v_v_202_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_v_202_);
if (v_isSharedCheck_235_ == 0)
{
v___x_225_ = v_v_202_;
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_node_223_);
lean_dec(v_v_202_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_227_ = ((size_t)5ULL);
v___x_228_ = lean_usize_shift_right(v_x_189_, v___x_227_);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_x_190_, v___x_229_);
v___x_231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_223_, v___x_228_, v___x_230_, v_x_191_, v_x_192_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_231_);
v___x_233_ = v___x_225_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v___y_206_ = v___x_233_;
goto v___jp_205_;
}
}
}
default: 
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_x_191_);
lean_ctor_set(v___x_236_, 1, v_x_192_);
v___y_206_ = v___x_236_;
goto v___jp_205_;
}
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_array_fset(v_xs_x27_204_, v_j_196_, v___y_206_);
lean_dec(v_j_196_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_207_);
v___x_209_ = v___x_200_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
else
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_258_; 
v_ks_239_ = lean_ctor_get(v_x_188_, 0);
v_vs_240_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_258_ == 0)
{
v___x_242_ = v_x_188_;
v_isShared_243_ = v_isSharedCheck_258_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_vs_240_);
lean_inc(v_ks_239_);
lean_dec(v_x_188_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_258_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_ks_239_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_vs_240_);
v___x_245_ = v_reuseFailAlloc_257_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v_newNode_246_; size_t v___x_247_; uint8_t v___x_248_; 
v_newNode_246_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_245_, v_x_191_, v_x_192_);
v___x_247_ = ((size_t)7ULL);
v___x_248_ = lean_usize_dec_le(v___x_247_, v_x_190_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_246_);
v___x_250_ = lean_unsigned_to_nat(4u);
v___x_251_ = lean_nat_dec_lt(v___x_249_, v___x_250_);
lean_dec(v___x_249_);
if (v___x_251_ == 0)
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_ks_252_ = lean_ctor_get(v_newNode_246_, 0);
lean_inc_ref(v_ks_252_);
v_vs_253_ = lean_ctor_get(v_newNode_246_, 1);
lean_inc_ref(v_vs_253_);
lean_dec_ref(v_newNode_246_);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_190_, v_ks_252_, v_vs_253_, v___x_254_, v___x_255_);
lean_dec_ref(v_vs_253_);
lean_dec_ref(v_ks_252_);
return v___x_256_;
}
else
{
return v_newNode_246_;
}
}
else
{
return v_newNode_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_259_, lean_object* v_keys_260_, lean_object* v_vals_261_, lean_object* v_i_262_, lean_object* v_entries_263_){
_start:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_array_get_size(v_keys_260_);
v___x_265_ = lean_nat_dec_lt(v_i_262_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v_i_262_);
return v_entries_263_;
}
else
{
lean_object* v_k_266_; lean_object* v_v_267_; uint64_t v___y_269_; 
v_k_266_ = lean_array_fget_borrowed(v_keys_260_, v_i_262_);
v_v_267_ = lean_array_fget_borrowed(v_vals_261_, v_i_262_);
if (lean_obj_tag(v_k_266_) == 0)
{
uint64_t v___x_280_; 
v___x_280_ = 1723ULL;
v___y_269_ = v___x_280_;
goto v___jp_268_;
}
else
{
uint64_t v_hash_281_; 
v_hash_281_ = lean_ctor_get_uint64(v_k_266_, sizeof(void*)*2);
v___y_269_ = v_hash_281_;
goto v___jp_268_;
}
v___jp_268_:
{
size_t v_h_270_; size_t v___x_271_; lean_object* v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v_h_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_h_270_ = lean_uint64_to_usize(v___y_269_);
v___x_271_ = ((size_t)5ULL);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_sub(v_depth_259_, v___x_273_);
v___x_275_ = lean_usize_mul(v___x_271_, v___x_274_);
v_h_276_ = lean_usize_shift_right(v_h_270_, v___x_275_);
v___x_277_ = lean_nat_add(v_i_262_, v___x_272_);
lean_dec(v_i_262_);
lean_inc(v_v_267_);
lean_inc(v_k_266_);
v___x_278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_263_, v_h_276_, v_depth_259_, v_k_266_, v_v_267_);
v_i_262_ = v___x_277_;
v_entries_263_ = v___x_278_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_282_, lean_object* v_keys_283_, lean_object* v_vals_284_, lean_object* v_i_285_, lean_object* v_entries_286_){
_start:
{
size_t v_depth_boxed_287_; lean_object* v_res_288_; 
v_depth_boxed_287_ = lean_unbox_usize(v_depth_282_);
lean_dec(v_depth_282_);
v_res_288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_287_, v_keys_283_, v_vals_284_, v_i_285_, v_entries_286_);
lean_dec_ref(v_vals_284_);
lean_dec_ref(v_keys_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
size_t v_x_1075__boxed_294_; size_t v_x_1076__boxed_295_; lean_object* v_res_296_; 
v_x_1075__boxed_294_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_x_1076__boxed_295_ = lean_unbox_usize(v_x_291_);
lean_dec(v_x_291_);
v_res_296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_289_, v_x_1075__boxed_294_, v_x_1076__boxed_295_, v_x_292_, v_x_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
uint64_t v___y_301_; 
if (lean_obj_tag(v_x_298_) == 0)
{
uint64_t v___x_305_; 
v___x_305_ = 1723ULL;
v___y_301_ = v___x_305_;
goto v___jp_300_;
}
else
{
uint64_t v_hash_306_; 
v_hash_306_ = lean_ctor_get_uint64(v_x_298_, sizeof(void*)*2);
v___y_301_ = v_hash_306_;
goto v___jp_300_;
}
v___jp_300_:
{
size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_uint64_to_usize(v___y_301_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_297_, v___x_302_, v___x_303_, v_x_298_, v_x_299_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
return v_x_307_;
}
else
{
lean_object* v_key_309_; lean_object* v_value_310_; lean_object* v_tail_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_337_; 
v_key_309_ = lean_ctor_get(v_x_308_, 0);
v_value_310_ = lean_ctor_get(v_x_308_, 1);
v_tail_311_ = lean_ctor_get(v_x_308_, 2);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_337_ == 0)
{
v___x_313_ = v_x_308_;
v_isShared_314_ = v_isSharedCheck_337_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_tail_311_);
lean_inc(v_value_310_);
lean_inc(v_key_309_);
lean_dec(v_x_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_337_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; uint64_t v___y_317_; 
v___x_315_ = lean_array_get_size(v_x_307_);
if (lean_obj_tag(v_key_309_) == 0)
{
uint64_t v___x_335_; 
v___x_335_ = 1723ULL;
v___y_317_ = v___x_335_;
goto v___jp_316_;
}
else
{
uint64_t v_hash_336_; 
v_hash_336_ = lean_ctor_get_uint64(v_key_309_, sizeof(void*)*2);
v___y_317_ = v_hash_336_;
goto v___jp_316_;
}
v___jp_316_:
{
uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v_fold_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_318_ = 32ULL;
v___x_319_ = lean_uint64_shift_right(v___y_317_, v___x_318_);
v_fold_320_ = lean_uint64_xor(v___y_317_, v___x_319_);
v___x_321_ = 16ULL;
v___x_322_ = lean_uint64_shift_right(v_fold_320_, v___x_321_);
v___x_323_ = lean_uint64_xor(v_fold_320_, v___x_322_);
v___x_324_ = lean_uint64_to_usize(v___x_323_);
v___x_325_ = lean_usize_of_nat(v___x_315_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_sub(v___x_325_, v___x_326_);
v___x_328_ = lean_usize_land(v___x_324_, v___x_327_);
v___x_329_ = lean_array_uget_borrowed(v_x_307_, v___x_328_);
lean_inc(v___x_329_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 2, v___x_329_);
v___x_331_ = v___x_313_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_key_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_value_310_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v___x_329_);
v___x_331_ = v_reuseFailAlloc_334_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; 
v___x_332_ = lean_array_uset(v_x_307_, v___x_328_, v___x_331_);
v_x_307_ = v___x_332_;
v_x_308_ = v_tail_311_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_338_, lean_object* v_source_339_, lean_object* v_target_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_array_get_size(v_source_339_);
v___x_342_ = lean_nat_dec_lt(v_i_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec_ref(v_source_339_);
lean_dec(v_i_338_);
return v_target_340_;
}
else
{
lean_object* v_es_343_; lean_object* v___x_344_; lean_object* v_source_345_; lean_object* v_target_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_es_343_ = lean_array_fget(v_source_339_, v_i_338_);
v___x_344_ = lean_box(0);
v_source_345_ = lean_array_fset(v_source_339_, v_i_338_, v___x_344_);
v_target_346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_340_, v_es_343_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_i_338_, v___x_347_);
lean_dec(v_i_338_);
v_i_338_ = v___x_348_;
v_source_339_ = v_source_345_;
v_target_340_ = v_target_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_nbuckets_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_351_ = lean_array_get_size(v_data_350_);
v___x_352_ = lean_unsigned_to_nat(2u);
v_nbuckets_353_ = lean_nat_mul(v___x_351_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_box(0);
v___x_356_ = lean_mk_array(v_nbuckets_353_, v___x_355_);
v___x_357_ = lean_array_propagate_mark(v_data_350_, v___x_356_);
v___x_358_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_354_, v_data_350_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
uint8_t v___x_361_; 
v___x_361_ = 0;
return v___x_361_;
}
else
{
lean_object* v_key_362_; lean_object* v_tail_363_; uint8_t v___x_364_; 
v_key_362_ = lean_ctor_get(v_x_360_, 0);
v_tail_363_ = lean_ctor_get(v_x_360_, 2);
v___x_364_ = lean_name_eq(v_key_362_, v_a_359_);
if (v___x_364_ == 0)
{
v_x_360_ = v_tail_363_;
goto _start;
}
else
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_366_, v_x_367_);
lean_dec(v_x_367_);
lean_dec(v_a_366_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_370_, lean_object* v_b_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_dec(v_b_371_);
lean_dec(v_a_370_);
return v_x_372_;
}
else
{
lean_object* v_key_373_; lean_object* v_value_374_; lean_object* v_tail_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_key_373_ = lean_ctor_get(v_x_372_, 0);
v_value_374_ = lean_ctor_get(v_x_372_, 1);
v_tail_375_ = lean_ctor_get(v_x_372_, 2);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v_x_372_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_tail_375_);
lean_inc(v_value_374_);
lean_inc(v_key_373_);
lean_dec(v_x_372_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = lean_name_eq(v_key_373_, v_a_370_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_370_, v_b_371_, v_tail_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 2, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_key_373_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_value_374_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_385_; 
lean_dec(v_value_374_);
lean_dec(v_key_373_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_b_371_);
lean_ctor_set(v___x_377_, 0, v_a_370_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_370_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_b_371_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_tail_375_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v_size_391_; lean_object* v_buckets_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_438_; 
v_size_391_ = lean_ctor_get(v_m_388_, 0);
v_buckets_392_ = lean_ctor_get(v_m_388_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_m_388_);
if (v_isSharedCheck_438_ == 0)
{
v___x_394_ = v_m_388_;
v_isShared_395_ = v_isSharedCheck_438_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_buckets_392_);
lean_inc(v_size_391_);
lean_dec(v_m_388_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_438_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; uint64_t v___y_398_; 
v___x_396_ = lean_array_get_size(v_buckets_392_);
if (lean_obj_tag(v_a_389_) == 0)
{
uint64_t v___x_436_; 
v___x_436_ = 1723ULL;
v___y_398_ = v___x_436_;
goto v___jp_397_;
}
else
{
uint64_t v_hash_437_; 
v_hash_437_ = lean_ctor_get_uint64(v_a_389_, sizeof(void*)*2);
v___y_398_ = v_hash_437_;
goto v___jp_397_;
}
v___jp_397_:
{
uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v_fold_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v_bkt_410_; uint8_t v___x_411_; 
v___x_399_ = 32ULL;
v___x_400_ = lean_uint64_shift_right(v___y_398_, v___x_399_);
v_fold_401_ = lean_uint64_xor(v___y_398_, v___x_400_);
v___x_402_ = 16ULL;
v___x_403_ = lean_uint64_shift_right(v_fold_401_, v___x_402_);
v___x_404_ = lean_uint64_xor(v_fold_401_, v___x_403_);
v___x_405_ = lean_uint64_to_usize(v___x_404_);
v___x_406_ = lean_usize_of_nat(v___x_396_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_sub(v___x_406_, v___x_407_);
v___x_409_ = lean_usize_land(v___x_405_, v___x_408_);
v_bkt_410_ = lean_array_uget_borrowed(v_buckets_392_, v___x_409_);
v___x_411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_389_, v_bkt_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v_size_x27_413_; lean_object* v___x_414_; lean_object* v_buckets_x27_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v_size_x27_413_ = lean_nat_add(v_size_391_, v___x_412_);
lean_dec(v_size_391_);
lean_inc(v_bkt_410_);
v___x_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_414_, 0, v_a_389_);
lean_ctor_set(v___x_414_, 1, v_b_390_);
lean_ctor_set(v___x_414_, 2, v_bkt_410_);
v_buckets_x27_415_ = lean_array_uset(v_buckets_392_, v___x_409_, v___x_414_);
v___x_416_ = lean_unsigned_to_nat(4u);
v___x_417_ = lean_nat_mul(v_size_x27_413_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(3u);
v___x_419_ = lean_nat_div(v___x_417_, v___x_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_array_get_size(v_buckets_x27_415_);
v___x_421_ = lean_nat_dec_le(v___x_419_, v___x_420_);
lean_dec(v___x_419_);
if (v___x_421_ == 0)
{
lean_object* v_val_422_; lean_object* v___x_424_; 
v_val_422_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_415_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v_val_422_);
lean_ctor_set(v___x_394_, 0, v_size_x27_413_);
v___x_424_ = v___x_394_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_size_x27_413_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_val_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v___x_427_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v_buckets_x27_415_);
lean_ctor_set(v___x_394_, 0, v_size_x27_413_);
v___x_427_ = v___x_394_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_size_x27_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_buckets_x27_415_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v___x_429_; lean_object* v_buckets_x27_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_bkt_410_);
v___x_429_ = lean_box(0);
v_buckets_x27_430_ = lean_array_uset(v_buckets_392_, v___x_409_, v___x_429_);
v___x_431_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_389_, v_b_390_, v_bkt_410_);
v___x_432_ = lean_array_uset(v_buckets_x27_430_, v___x_409_, v___x_431_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_432_);
v___x_434_ = v___x_394_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_size_391_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_stage_u2081_442_; 
v_stage_u2081_442_ = lean_ctor_get_uint8(v_x_439_, sizeof(void*)*2);
if (v_stage_u2081_442_ == 0)
{
lean_object* v_map_u2081_443_; lean_object* v_map_u2082_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_map_u2081_443_ = lean_ctor_get(v_x_439_, 0);
v_map_u2082_444_ = lean_ctor_get(v_x_439_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v_x_439_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_map_u2082_444_);
lean_inc(v_map_u2081_443_);
lean_dec(v_x_439_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_444_, v_x_440_, v_x_441_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_map_u2081_443_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_451_, sizeof(void*)*2, v_stage_u2081_442_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v_map_u2081_453_; lean_object* v_map_u2082_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_462_; 
v_map_u2081_453_ = lean_ctor_get(v_x_439_, 0);
v_map_u2082_454_ = lean_ctor_get(v_x_439_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_462_ == 0)
{
v___x_456_ = v_x_439_;
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_map_u2082_454_);
lean_inc(v_map_u2081_453_);
lean_dec(v_x_439_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_453_, v_x_440_, v_x_441_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_map_u2082_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_461_, sizeof(void*)*2, v_stage_u2081_442_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v_key_466_; lean_object* v_value_467_; lean_object* v_tail_468_; uint8_t v___x_469_; 
v_key_466_ = lean_ctor_get(v_x_464_, 0);
v_value_467_ = lean_ctor_get(v_x_464_, 1);
v_tail_468_ = lean_ctor_get(v_x_464_, 2);
v___x_469_ = lean_name_eq(v_key_466_, v_a_463_);
if (v___x_469_ == 0)
{
v_x_464_ = v_tail_468_;
goto _start;
}
else
{
lean_object* v___x_471_; 
lean_inc(v_value_467_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_value_467_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_472_, v_x_473_);
lean_dec(v_x_473_);
lean_dec(v_a_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_buckets_477_; lean_object* v___x_478_; uint64_t v___y_480_; 
v_buckets_477_ = lean_ctor_get(v_m_475_, 1);
v___x_478_ = lean_array_get_size(v_buckets_477_);
if (lean_obj_tag(v_a_476_) == 0)
{
uint64_t v___x_494_; 
v___x_494_ = 1723ULL;
v___y_480_ = v___x_494_;
goto v___jp_479_;
}
else
{
uint64_t v_hash_495_; 
v_hash_495_ = lean_ctor_get_uint64(v_a_476_, sizeof(void*)*2);
v___y_480_ = v_hash_495_;
goto v___jp_479_;
}
v___jp_479_:
{
uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v_fold_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_481_ = 32ULL;
v___x_482_ = lean_uint64_shift_right(v___y_480_, v___x_481_);
v_fold_483_ = lean_uint64_xor(v___y_480_, v___x_482_);
v___x_484_ = 16ULL;
v___x_485_ = lean_uint64_shift_right(v_fold_483_, v___x_484_);
v___x_486_ = lean_uint64_xor(v_fold_483_, v___x_485_);
v___x_487_ = lean_uint64_to_usize(v___x_486_);
v___x_488_ = lean_usize_of_nat(v___x_478_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_sub(v___x_488_, v___x_489_);
v___x_491_ = lean_usize_land(v___x_487_, v___x_490_);
v___x_492_ = lean_array_uget_borrowed(v_buckets_477_, v___x_491_);
v___x_493_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_476_, v___x_492_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_m_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_499_, lean_object* v_vals_500_, lean_object* v_i_501_, lean_object* v_k_502_){
_start:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_get_size(v_keys_499_);
v___x_504_ = lean_nat_dec_lt(v_i_501_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v_i_501_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
else
{
lean_object* v_k_x27_506_; uint8_t v___x_507_; 
v_k_x27_506_ = lean_array_fget_borrowed(v_keys_499_, v_i_501_);
v___x_507_ = lean_name_eq(v_k_502_, v_k_x27_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_i_501_, v___x_508_);
lean_dec(v_i_501_);
v_i_501_ = v___x_509_;
goto _start;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_array_fget_borrowed(v_vals_500_, v_i_501_);
lean_dec(v_i_501_);
lean_inc(v___x_511_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_513_, lean_object* v_vals_514_, lean_object* v_i_515_, lean_object* v_k_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_513_, v_vals_514_, v_i_515_, v_k_516_);
lean_dec(v_k_516_);
lean_dec_ref(v_vals_514_);
lean_dec_ref(v_keys_513_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_518_, size_t v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_object* v_es_521_; lean_object* v___x_522_; size_t v___x_523_; size_t v___x_524_; lean_object* v_j_525_; lean_object* v___x_526_; 
v_es_521_ = lean_ctor_get(v_x_518_, 0);
v___x_522_ = lean_box(2);
v___x_523_ = ((size_t)31ULL);
v___x_524_ = lean_usize_land(v_x_519_, v___x_523_);
v_j_525_ = lean_usize_to_nat(v___x_524_);
v___x_526_ = lean_array_get_borrowed(v___x_522_, v_es_521_, v_j_525_);
lean_dec(v_j_525_);
switch(lean_obj_tag(v___x_526_))
{
case 0:
{
lean_object* v_key_527_; lean_object* v_val_528_; uint8_t v___x_529_; 
v_key_527_ = lean_ctor_get(v___x_526_, 0);
v_val_528_ = lean_ctor_get(v___x_526_, 1);
v___x_529_ = lean_name_eq(v_x_520_, v_key_527_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
v___x_530_ = lean_box(0);
return v___x_530_;
}
else
{
lean_object* v___x_531_; 
lean_inc(v_val_528_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v_val_528_);
return v___x_531_;
}
}
case 1:
{
lean_object* v_node_532_; size_t v___x_533_; size_t v___x_534_; 
v_node_532_ = lean_ctor_get(v___x_526_, 0);
v___x_533_ = ((size_t)5ULL);
v___x_534_ = lean_usize_shift_right(v_x_519_, v___x_533_);
v_x_518_ = v_node_532_;
v_x_519_ = v___x_534_;
goto _start;
}
default: 
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(0);
return v___x_536_;
}
}
}
else
{
lean_object* v_ks_537_; lean_object* v_vs_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_ks_537_ = lean_ctor_get(v_x_518_, 0);
v_vs_538_ = lean_ctor_get(v_x_518_, 1);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_537_, v_vs_538_, v___x_539_, v_x_520_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
size_t v_x_1579__boxed_544_; lean_object* v_res_545_; 
v_x_1579__boxed_544_ = lean_unbox_usize(v_x_542_);
lean_dec(v_x_542_);
v_res_545_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_541_, v_x_1579__boxed_544_, v_x_543_);
lean_dec(v_x_543_);
lean_dec_ref(v_x_541_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
uint64_t v___y_549_; 
if (lean_obj_tag(v_x_547_) == 0)
{
uint64_t v___x_552_; 
v___x_552_ = 1723ULL;
v___y_549_ = v___x_552_;
goto v___jp_548_;
}
else
{
uint64_t v_hash_553_; 
v_hash_553_ = lean_ctor_get_uint64(v_x_547_, sizeof(void*)*2);
v___y_549_ = v_hash_553_;
goto v___jp_548_;
}
v___jp_548_:
{
size_t v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_uint64_to_usize(v___y_549_);
v___x_551_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_546_, v___x_550_, v_x_547_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_554_, v_x_555_);
lean_dec(v_x_555_);
lean_dec_ref(v_x_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
uint8_t v_stage_u2081_559_; 
v_stage_u2081_559_ = lean_ctor_get_uint8(v_x_557_, sizeof(void*)*2);
if (v_stage_u2081_559_ == 0)
{
lean_object* v_map_u2081_560_; lean_object* v_map_u2082_561_; lean_object* v___x_562_; 
v_map_u2081_560_ = lean_ctor_get(v_x_557_, 0);
v_map_u2082_561_ = lean_ctor_get(v_x_557_, 1);
v___x_562_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_561_, v_x_558_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_560_, v_x_558_);
return v___x_563_;
}
else
{
return v___x_562_;
}
}
else
{
lean_object* v_map_u2081_564_; lean_object* v___x_565_; 
v_map_u2081_564_ = lean_ctor_get(v_x_557_, 0);
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_564_, v_x_558_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_566_, v_x_567_);
lean_dec(v_x_567_);
lean_dec_ref(v_x_566_);
return v_res_568_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
uint8_t v___x_571_; 
v___x_571_ = 0;
return v___x_571_;
}
else
{
lean_object* v_head_572_; lean_object* v_tail_573_; uint8_t v___x_574_; 
v_head_572_ = lean_ctor_get(v_x_570_, 0);
v_tail_573_ = lean_ctor_get(v_x_570_, 1);
v___x_574_ = lean_name_eq(v_a_569_, v_head_572_);
if (v___x_574_ == 0)
{
v_x_570_ = v_tail_573_;
goto _start;
}
else
{
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_576_, lean_object* v_x_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec(v_a_576_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_580_, lean_object* v_e_581_){
_start:
{
lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_599_; 
v_fst_582_ = lean_ctor_get(v_e_581_, 0);
v_snd_583_ = lean_ctor_get(v_e_581_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_e_581_);
if (v_isSharedCheck_599_ == 0)
{
v___x_585_ = v_e_581_;
v_isShared_586_ = v_isSharedCheck_599_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_snd_583_);
lean_inc(v_fst_582_);
lean_dec(v_e_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_599_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_580_, v_fst_582_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 1);
lean_ctor_set(v___x_585_, 1, v___x_588_);
lean_ctor_set(v___x_585_, 0, v_snd_583_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_snd_583_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_592_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_580_, v_fst_582_, v___x_590_);
return v___x_591_;
}
}
else
{
lean_object* v_val_593_; uint8_t v___x_594_; 
v_val_593_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_587_, 1);
v___x_594_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_583_, v_val_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_596_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 1);
lean_ctor_set(v___x_585_, 1, v_val_593_);
lean_ctor_set(v___x_585_, 0, v_snd_583_);
v___x_596_ = v___x_585_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_snd_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_val_593_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_580_, v_fst_582_, v___x_596_);
return v___x_597_;
}
}
else
{
lean_dec(v_val_593_);
lean_del_object(v___x_585_);
lean_dec(v_snd_583_);
lean_dec(v_fst_582_);
return v_s_580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_604_, v_x_605_, v_x_606_);
lean_dec(v_x_606_);
lean_dec_ref(v_x_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_609_, v_x_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_617_, v_x_618_, v_x_619_);
lean_dec(v_x_619_);
lean_dec_ref(v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_621_, lean_object* v_m_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_622_, v_a_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_625_, v_m_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_m_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_630_, v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_634_, lean_object* v_m_635_, lean_object* v_a_636_, lean_object* v_b_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_635_, v_a_636_, v_b_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_639_, lean_object* v_x_640_, size_t v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_640_, v_x_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_644_, lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
size_t v_x_1744__boxed_648_; lean_object* v_res_649_; 
v_x_1744__boxed_648_ = lean_unbox_usize(v_x_646_);
lean_dec(v_x_646_);
v_res_649_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_644_, v_x_645_, v_x_1744__boxed_648_, v_x_647_);
lean_dec(v_x_647_);
lean_dec_ref(v_x_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_650_, lean_object* v_a_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_654_, lean_object* v_a_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_654_, v_a_655_, v_x_656_);
lean_dec(v_x_656_);
lean_dec(v_a_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, size_t v_x_660_, size_t v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_659_, v_x_660_, v_x_661_, v_x_662_, v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
size_t v_x_1760__boxed_671_; size_t v_x_1761__boxed_672_; lean_object* v_res_673_; 
v_x_1760__boxed_671_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_x_1761__boxed_672_ = lean_unbox_usize(v_x_668_);
lean_dec(v_x_668_);
v_res_673_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_665_, v_x_666_, v_x_1760__boxed_671_, v_x_1761__boxed_672_, v_x_669_, v_x_670_);
return v_res_673_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_678_, lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_678_, v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec(v_a_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_683_, lean_object* v_data_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_686_, lean_object* v_a_687_, lean_object* v_b_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_687_, v_b_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_691_, lean_object* v_keys_692_, lean_object* v_vals_693_, lean_object* v_heq_694_, lean_object* v_i_695_, lean_object* v_k_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_692_, v_vals_693_, v_i_695_, v_k_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_698_, lean_object* v_keys_699_, lean_object* v_vals_700_, lean_object* v_heq_701_, lean_object* v_i_702_, lean_object* v_k_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_698_, v_keys_699_, v_vals_700_, v_heq_701_, v_i_702_, v_k_703_);
lean_dec(v_k_703_);
lean_dec_ref(v_vals_700_);
lean_dec_ref(v_keys_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_705_, lean_object* v_n_706_, lean_object* v_k_707_, lean_object* v_v_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_706_, v_k_707_, v_v_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_710_, size_t v_depth_711_, lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_heq_714_, lean_object* v_i_715_, lean_object* v_entries_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_711_, v_keys_712_, v_vals_713_, v_i_715_, v_entries_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_718_, lean_object* v_depth_719_, lean_object* v_keys_720_, lean_object* v_vals_721_, lean_object* v_heq_722_, lean_object* v_i_723_, lean_object* v_entries_724_){
_start:
{
size_t v_depth_boxed_725_; lean_object* v_res_726_; 
v_depth_boxed_725_ = lean_unbox_usize(v_depth_719_);
lean_dec(v_depth_719_);
v_res_726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_718_, v_depth_boxed_725_, v_keys_720_, v_vals_721_, v_heq_722_, v_i_723_, v_entries_724_);
lean_dec_ref(v_vals_721_);
lean_dec_ref(v_keys_720_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_727_, lean_object* v_i_728_, lean_object* v_source_729_, lean_object* v_target_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_728_, v_source_729_, v_target_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_733_, v_x_734_, v_x_735_, v_x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_742_){
_start:
{
uint8_t v_stage_u2081_743_; 
v_stage_u2081_743_ = lean_ctor_get_uint8(v_m_742_, sizeof(void*)*2);
if (v_stage_u2081_743_ == 0)
{
return v_m_742_;
}
else
{
lean_object* v_map_u2081_744_; lean_object* v_map_u2082_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_map_u2081_744_ = lean_ctor_get(v_m_742_, 0);
v_map_u2082_745_ = lean_ctor_get(v_m_742_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_m_742_);
if (v_isSharedCheck_753_ == 0)
{
v___x_747_ = v_m_742_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_map_u2082_745_);
lean_inc(v_map_u2081_744_);
lean_dec(v_m_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
uint8_t v___x_749_; lean_object* v___x_751_; 
v___x_749_ = 0;
if (v_isShared_748_ == 0)
{
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_map_u2081_744_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_map_u2082_745_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*2, v___x_749_);
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_754_, lean_object* v_m_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_array_mk(v_es_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_, lean_object* v_b_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; size_t v___x_766_; size_t v___x_767_; 
v___x_764_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
lean_inc(v___x_764_);
v___x_765_ = l_Lean_addAliasEntry(v_b_762_, v___x_764_);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_760_, v___x_766_);
v_i_760_ = v___x_767_;
v_b_762_ = v___x_765_;
goto _start;
}
else
{
return v_b_762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_769_, lean_object* v_i_770_, lean_object* v_stop_771_, lean_object* v_b_772_){
_start:
{
size_t v_i_boxed_773_; size_t v_stop_boxed_774_; lean_object* v_res_775_; 
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_stop_boxed_774_ = lean_unbox_usize(v_stop_771_);
lean_dec(v_stop_771_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_769_, v_i_boxed_773_, v_stop_boxed_774_, v_b_772_);
lean_dec_ref(v_as_769_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_776_, size_t v_i_777_, size_t v_stop_778_, lean_object* v_b_779_){
_start:
{
lean_object* v___y_781_; uint8_t v___x_785_; 
v___x_785_ = lean_usize_dec_eq(v_i_777_, v_stop_778_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_786_ = lean_array_uget_borrowed(v_as_776_, v_i_777_);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_array_get_size(v___x_786_);
v___x_789_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
v___y_781_ = v_b_779_;
goto v___jp_780_;
}
else
{
size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_788_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_786_, v___x_790_, v___x_791_, v_b_779_);
v___y_781_ = v___x_792_;
goto v___jp_780_;
}
}
else
{
return v_b_779_;
}
v___jp_780_:
{
size_t v___x_782_; size_t v___x_783_; 
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_add(v_i_777_, v___x_782_);
v_i_777_ = v___x_783_;
v_b_779_ = v___y_781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_793_, lean_object* v_i_794_, lean_object* v_stop_795_, lean_object* v_b_796_){
_start:
{
size_t v_i_boxed_797_; size_t v_stop_boxed_798_; lean_object* v_res_799_; 
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_stop_boxed_798_ = lean_unbox_usize(v_stop_795_);
lean_dec(v_stop_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_793_, v_i_boxed_797_, v_stop_boxed_798_, v_b_796_);
lean_dec_ref(v_as_793_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_800_, lean_object* v_as_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_array_get_size(v_as_801_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
return v_initState_800_;
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_803_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_801_, v___x_805_, v___x_806_, v_initState_800_);
return v___x_807_;
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
v___x_817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_846_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
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
LEAN_EXPORT lean_object* l_Lean_addAlias___lam__0(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_s_852_){
_start:
{
lean_object* v_addEntryFn_853_; lean_object* v_importedEntries_854_; lean_object* v_state_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_863_; 
v_addEntryFn_853_ = lean_ctor_get(v___x_850_, 3);
lean_inc(v_addEntryFn_853_);
lean_dec_ref(v___x_850_);
v_importedEntries_854_ = lean_ctor_get(v_s_852_, 0);
v_state_855_ = lean_ctor_get(v_s_852_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_s_852_);
if (v_isSharedCheck_863_ == 0)
{
v___x_857_ = v_s_852_;
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_state_855_);
lean_inc(v_importedEntries_854_);
lean_dec(v_s_852_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_state_859_; lean_object* v___x_861_; 
v_state_859_ = lean_apply_2(v_addEntryFn_853_, v_state_855_, v___x_851_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_state_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_importedEntries_854_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_state_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_864_, lean_object* v_a_865_, lean_object* v_e_866_){
_start:
{
lean_object* v___x_867_; lean_object* v_toEnvExtension_868_; lean_object* v_asyncMode_869_; uint8_t v_logWrites_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_867_ = l_Lean_aliasExtension;
v_toEnvExtension_868_ = lean_ctor_get(v___x_867_, 0);
v_asyncMode_869_ = lean_ctor_get(v_toEnvExtension_868_, 2);
v_logWrites_870_ = lean_ctor_get_uint8(v_toEnvExtension_868_, sizeof(void*)*6);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_a_865_);
lean_ctor_set(v___x_871_, 1, v_e_866_);
v___f_872_ = lean_alloc_closure((void*)(l_Lean_addAlias___lam__0), 3, 2);
lean_closure_set(v___f_872_, 0, v___x_867_);
lean_closure_set(v___f_872_, 1, v___x_871_);
v___x_873_ = lean_box(0);
v___x_874_ = 1;
if (v_logWrites_870_ == 0)
{
lean_object* v___x_875_; 
lean_inc_ref(v_toEnvExtension_868_);
v___x_875_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_868_, v_env_864_, v___f_872_, v_asyncMode_869_, v___x_873_, v___x_874_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc_ref_n(v_toEnvExtension_868_, 2);
v___x_876_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_868_, v_env_864_);
lean_dec_ref(v_env_864_);
v___x_877_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_868_, v___x_876_, v___f_872_, v_asyncMode_869_, v___x_873_, v___x_874_);
return v___x_877_;
}
}
}
static lean_object* _init_l_Lean_getAliasState___closed__0(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_SMap_instInhabited___redArg();
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_879_){
_start:
{
lean_object* v___x_880_; lean_object* v_toEnvExtension_881_; lean_object* v_asyncMode_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = l_Lean_aliasExtension;
v_toEnvExtension_881_ = lean_ctor_get(v___x_880_, 0);
v_asyncMode_882_ = lean_ctor_get(v_toEnvExtension_881_, 2);
v___x_883_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_884_ = lean_box(0);
v___x_885_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_883_, v___x_880_, v_env_879_, v_asyncMode_882_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_886_, uint8_t v_skipProtected_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_object* v___x_890_; 
lean_dec_ref(v_env_886_);
v___x_890_ = l_List_reverse___redArg(v_a_889_);
return v___x_890_;
}
else
{
lean_object* v_head_891_; lean_object* v_tail_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_903_; 
v_head_891_ = lean_ctor_get(v_a_888_, 0);
v_tail_892_ = lean_ctor_get(v_a_888_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_903_ == 0)
{
v___x_894_ = v_a_888_;
v_isShared_895_ = v_isSharedCheck_903_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_tail_892_);
lean_inc(v_head_891_);
lean_dec(v_a_888_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_903_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
uint8_t v___x_896_; 
lean_inc(v_head_891_);
lean_inc_ref(v_env_886_);
v___x_896_ = l_Lean_isProtected(v_env_886_, v_head_891_);
if (v___x_896_ == 0)
{
if (v_skipProtected_887_ == 0)
{
lean_del_object(v___x_894_);
lean_dec(v_head_891_);
v_a_888_ = v_tail_892_;
goto _start;
}
else
{
lean_object* v___x_899_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_a_889_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_head_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_a_889_);
v___x_899_ = v_reuseFailAlloc_901_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
v_a_888_ = v_tail_892_;
v_a_889_ = v___x_899_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_894_);
lean_dec(v_head_891_);
v_a_888_ = v_tail_892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_904_, lean_object* v_skipProtected_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_skipProtected_boxed_908_; lean_object* v_res_909_; 
v_skipProtected_boxed_908_ = lean_unbox(v_skipProtected_905_);
v_res_909_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_904_, v_skipProtected_boxed_908_, v_a_906_, v_a_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_910_, lean_object* v_a_911_, uint8_t v_skipProtected_912_){
_start:
{
lean_object* v___x_913_; lean_object* v_toEnvExtension_914_; lean_object* v_asyncMode_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_913_ = l_Lean_aliasExtension;
v_toEnvExtension_914_ = lean_ctor_get(v___x_913_, 0);
v_asyncMode_915_ = lean_ctor_get(v_toEnvExtension_914_, 2);
v___x_916_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_917_ = lean_box(0);
lean_inc_ref(v_env_910_);
v___x_918_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_916_, v___x_913_, v_env_910_, v_asyncMode_915_, v___x_917_);
v___x_919_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_918_, v_a_911_);
lean_dec(v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; 
lean_dec_ref(v_env_910_);
v___x_920_ = lean_box(0);
return v___x_920_;
}
else
{
if (v_skipProtected_912_ == 0)
{
lean_object* v_val_921_; 
lean_dec_ref(v_env_910_);
v_val_921_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v___x_919_, 1);
return v_val_921_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_val_922_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v___x_919_, 1);
v___x_923_ = lean_box(0);
v___x_924_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_910_, v_skipProtected_912_, v_val_922_, v___x_923_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_925_, lean_object* v_a_926_, lean_object* v_skipProtected_927_){
_start:
{
uint8_t v_skipProtected_boxed_928_; lean_object* v_res_929_; 
v_skipProtected_boxed_928_ = lean_unbox(v_skipProtected_927_);
v_res_929_ = l_Lean_getAliases(v_env_925_, v_a_926_, v_skipProtected_boxed_928_);
lean_dec(v_a_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_930_, lean_object* v_as_931_, lean_object* v_a_932_, lean_object* v_es_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_930_, v_es_933_);
if (v___x_934_ == 0)
{
lean_dec(v_a_932_);
return v_as_931_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_935_, 0, v_a_932_);
lean_ctor_set(v___x_935_, 1, v_as_931_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_936_, lean_object* v_as_937_, lean_object* v_a_938_, lean_object* v_es_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_getRevAliases___lam__0(v_e_936_, v_as_937_, v_a_938_, v_es_939_);
lean_dec(v_es_939_);
lean_dec(v_e_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_i_944_, lean_object* v_acc_945_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_array_get_size(v_keys_942_);
v___x_947_ = lean_nat_dec_lt(v_i_944_, v___x_946_);
if (v___x_947_ == 0)
{
lean_dec(v_i_944_);
lean_dec(v_f_941_);
return v_acc_945_;
}
else
{
lean_object* v_k_948_; lean_object* v_v_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_k_948_ = lean_array_fget_borrowed(v_keys_942_, v_i_944_);
v_v_949_ = lean_array_fget_borrowed(v_vals_943_, v_i_944_);
lean_inc(v_f_941_);
lean_inc(v_v_949_);
lean_inc(v_k_948_);
v___x_950_ = lean_apply_3(v_f_941_, v_acc_945_, v_k_948_, v_v_949_);
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_add(v_i_944_, v___x_951_);
lean_dec(v_i_944_);
v_i_944_ = v___x_952_;
v_acc_945_ = v___x_950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_954_, lean_object* v_keys_955_, lean_object* v_vals_956_, lean_object* v_i_957_, lean_object* v_acc_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_954_, v_keys_955_, v_vals_956_, v_i_957_, v_acc_958_);
lean_dec_ref(v_vals_956_);
lean_dec_ref(v_keys_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_960_, lean_object* v_as_961_, size_t v_i_962_, size_t v_stop_963_, lean_object* v_b_964_){
_start:
{
lean_object* v___y_966_; uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_eq(v_i_962_, v_stop_963_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_array_uget_borrowed(v_as_961_, v_i_962_);
switch(lean_obj_tag(v___x_971_))
{
case 0:
{
lean_object* v_key_972_; lean_object* v_val_973_; lean_object* v___x_974_; 
v_key_972_ = lean_ctor_get(v___x_971_, 0);
v_val_973_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_f_960_);
lean_inc(v_val_973_);
lean_inc(v_key_972_);
v___x_974_ = lean_apply_3(v_f_960_, v_b_964_, v_key_972_, v_val_973_);
v___y_966_ = v___x_974_;
goto v___jp_965_;
}
case 1:
{
lean_object* v_node_975_; lean_object* v___x_976_; 
v_node_975_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_f_960_);
v___x_976_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_960_, v_node_975_, v_b_964_);
v___y_966_ = v___x_976_;
goto v___jp_965_;
}
default: 
{
v___y_966_ = v_b_964_;
goto v___jp_965_;
}
}
}
else
{
lean_dec(v_f_960_);
return v_b_964_;
}
v___jp_965_:
{
size_t v___x_967_; size_t v___x_968_; 
v___x_967_ = ((size_t)1ULL);
v___x_968_ = lean_usize_add(v_i_962_, v___x_967_);
v_i_962_ = v___x_968_;
v_b_964_ = v___y_966_;
goto _start;
}
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
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_982_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_977_, v_es_980_, v___x_984_, v___x_985_, v_x_979_);
return v___x_986_;
}
}
else
{
lean_object* v_ks_987_; lean_object* v_vs_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_ks_987_ = lean_ctor_get(v_x_978_, 0);
v_vs_988_ = lean_ctor_get(v_x_978_, 1);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_977_, v_ks_987_, v_vs_988_, v___x_989_, v_x_979_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_991_, v_x_992_, v_x_993_);
lean_dec_ref(v_x_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_995_, lean_object* v_as_996_, lean_object* v_i_997_, lean_object* v_stop_998_, lean_object* v_b_999_){
_start:
{
size_t v_i_boxed_1000_; size_t v_stop_boxed_1001_; lean_object* v_res_1002_; 
v_i_boxed_1000_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_stop_boxed_1001_ = lean_unbox_usize(v_stop_998_);
lean_dec(v_stop_998_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_995_, v_as_996_, v_i_boxed_1000_, v_stop_boxed_1001_, v_b_999_);
lean_dec_ref(v_as_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1003_, lean_object* v_x1_1004_, lean_object* v_x2_1005_, lean_object* v_x3_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_apply_3(v_f_1003_, v_x1_1004_, v_x2_1005_, v_x3_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1008_, lean_object* v_f_1009_, lean_object* v_init_1010_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1011_, 0, v_f_1009_);
v___x_1012_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1011_, v_map_1008_, v_init_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1013_, lean_object* v_f_1014_, lean_object* v_init_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1013_, v_f_1014_, v_init_1015_);
lean_dec_ref(v_map_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_dec(v_f_1017_);
return v_x_1018_;
}
else
{
lean_object* v_key_1020_; lean_object* v_value_1021_; lean_object* v_tail_1022_; lean_object* v___x_1023_; 
v_key_1020_ = lean_ctor_get(v_x_1019_, 0);
lean_inc(v_key_1020_);
v_value_1021_ = lean_ctor_get(v_x_1019_, 1);
lean_inc(v_value_1021_);
v_tail_1022_ = lean_ctor_get(v_x_1019_, 2);
lean_inc(v_tail_1022_);
lean_dec_ref_known(v_x_1019_, 3);
lean_inc(v_f_1017_);
v___x_1023_ = lean_apply_3(v_f_1017_, v_x_1018_, v_key_1020_, v_value_1021_);
v_x_1018_ = v___x_1023_;
v_x_1019_ = v_tail_1022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; 
v___x_1031_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
lean_inc(v___x_1031_);
lean_inc(v_f_1025_);
v___x_1032_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1025_, v_b_1029_, v___x_1031_);
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1027_, v___x_1033_);
v_i_1027_ = v___x_1034_;
v_b_1029_ = v___x_1032_;
goto _start;
}
else
{
lean_dec(v_f_1025_);
return v_b_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1036_, lean_object* v_as_1037_, lean_object* v_i_1038_, lean_object* v_stop_1039_, lean_object* v_b_1040_){
_start:
{
size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; lean_object* v_res_1043_; 
v_i_boxed_1041_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1039_);
lean_dec(v_stop_1039_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1036_, v_as_1037_, v_i_boxed_1041_, v_stop_boxed_1042_, v_b_1040_);
lean_dec_ref(v_as_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1044_, lean_object* v_init_1045_, lean_object* v_m_1046_){
_start:
{
lean_object* v_map_u2081_1047_; lean_object* v_map_u2082_1048_; lean_object* v_buckets_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_map_u2081_1047_ = lean_ctor_get(v_m_1046_, 0);
v_map_u2082_1048_ = lean_ctor_get(v_m_1046_, 1);
v_buckets_1049_ = lean_ctor_get(v_map_u2081_1047_, 1);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_array_get_size(v_buckets_1049_);
v___x_1052_ = lean_nat_dec_lt(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1048_, v_f_1044_, v_init_1045_);
return v___x_1053_;
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = lean_usize_of_nat(v___x_1051_);
lean_inc(v_f_1044_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1044_, v_buckets_1049_, v___x_1054_, v___x_1055_, v_init_1045_);
v___x_1057_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1048_, v_f_1044_, v___x_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1058_, lean_object* v_init_1059_, lean_object* v_m_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1058_, v_init_1059_, v_m_1060_);
lean_dec_ref(v_m_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1062_, lean_object* v_e_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v_toEnvExtension_1065_; lean_object* v_asyncMode_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1064_ = l_Lean_aliasExtension;
v_toEnvExtension_1065_ = lean_ctor_get(v___x_1064_, 0);
v_asyncMode_1066_ = lean_ctor_get(v_toEnvExtension_1065_, 2);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1067_, 0, v_e_1063_);
v___x_1068_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1068_, v___x_1064_, v_env_1062_, v_asyncMode_1066_, v___x_1070_);
v___x_1072_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1067_, v___x_1069_, v___x_1071_);
lean_dec(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1073_, lean_object* v_00_u03c3_1074_, lean_object* v_f_1075_, lean_object* v_init_1076_, lean_object* v_m_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1075_, v_init_1076_, v_m_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1079_, lean_object* v_00_u03c3_1080_, lean_object* v_f_1081_, lean_object* v_init_1082_, lean_object* v_m_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1079_, v_00_u03c3_1080_, v_f_1081_, v_init_1082_, v_m_1083_);
lean_dec_ref(v_m_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1085_, lean_object* v_00_u03c3_1086_, lean_object* v_f_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1087_, v_x_1088_, v_x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_map_1093_, lean_object* v_f_1094_, lean_object* v_init_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1093_, v_f_1094_, v_init_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_map_1099_, lean_object* v_f_1100_, lean_object* v_init_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1097_, v_00_u03b2_1098_, v_map_1099_, v_f_1100_, v_init_1101_);
lean_dec_ref(v_map_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1103_, lean_object* v_00_u03c3_1104_, lean_object* v_f_1105_, lean_object* v_as_1106_, size_t v_i_1107_, size_t v_stop_1108_, lean_object* v_b_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1105_, v_as_1106_, v_i_1107_, v_stop_1108_, v_b_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_00_u03c3_1112_, lean_object* v_f_1113_, lean_object* v_as_1114_, lean_object* v_i_1115_, lean_object* v_stop_1116_, lean_object* v_b_1117_){
_start:
{
size_t v_i_boxed_1118_; size_t v_stop_boxed_1119_; lean_object* v_res_1120_; 
v_i_boxed_1118_ = lean_unbox_usize(v_i_1115_);
lean_dec(v_i_1115_);
v_stop_boxed_1119_ = lean_unbox_usize(v_stop_1116_);
lean_dec(v_stop_1116_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1111_, v_00_u03c3_1112_, v_f_1113_, v_as_1114_, v_i_boxed_1118_, v_stop_boxed_1119_, v_b_1117_);
lean_dec_ref(v_as_1114_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1121_, lean_object* v_f_1122_, lean_object* v_init_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1122_, v_map_1121_, v_init_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1125_, lean_object* v_f_1126_, lean_object* v_init_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1125_, v_f_1126_, v_init_1127_);
lean_dec_ref(v_map_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_map_1131_, lean_object* v_f_1132_, lean_object* v_init_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1132_, v_map_1131_, v_init_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_map_1137_, lean_object* v_f_1138_, lean_object* v_init_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1135_, v_00_u03b2_1136_, v_map_1137_, v_f_1138_, v_init_1139_);
lean_dec_ref(v_map_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1141_, lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_f_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1144_, v_x_1145_, v_x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1148_, lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_f_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1148_, v_00_u03b1_1149_, v_00_u03b2_1150_, v_f_1151_, v_x_1152_, v_x_1153_);
lean_dec_ref(v_x_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_00_u03c3_1157_, lean_object* v_f_1158_, lean_object* v_as_1159_, size_t v_i_1160_, size_t v_stop_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1158_, v_as_1159_, v_i_1160_, v_stop_1161_, v_b_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_00_u03c3_1166_, lean_object* v_f_1167_, lean_object* v_as_1168_, lean_object* v_i_1169_, lean_object* v_stop_1170_, lean_object* v_b_1171_){
_start:
{
size_t v_i_boxed_1172_; size_t v_stop_boxed_1173_; lean_object* v_res_1174_; 
v_i_boxed_1172_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_stop_boxed_1173_ = lean_unbox_usize(v_stop_1170_);
lean_dec(v_stop_1170_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1164_, v_00_u03b2_1165_, v_00_u03c3_1166_, v_f_1167_, v_as_1168_, v_i_boxed_1172_, v_stop_boxed_1173_, v_b_1171_);
lean_dec_ref(v_as_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1175_, lean_object* v_00_u03b1_1176_, lean_object* v_00_u03b2_1177_, lean_object* v_f_1178_, lean_object* v_keys_1179_, lean_object* v_vals_1180_, lean_object* v_heq_1181_, lean_object* v_i_1182_, lean_object* v_acc_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1178_, v_keys_1179_, v_vals_1180_, v_i_1182_, v_acc_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1185_, lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_f_1188_, lean_object* v_keys_1189_, lean_object* v_vals_1190_, lean_object* v_heq_1191_, lean_object* v_i_1192_, lean_object* v_acc_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1185_, v_00_u03b1_1186_, v_00_u03b2_1187_, v_f_1188_, v_keys_1189_, v_vals_1190_, v_heq_1191_, v_i_1192_, v_acc_1193_);
lean_dec_ref(v_vals_1190_);
lean_dec_ref(v_keys_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1195_, lean_object* v_declName_1196_){
_start:
{
uint8_t v___y_1198_; uint8_t v___x_1201_; 
v___x_1201_ = l_Lean_Environment_containsOnBranch(v_env_1195_, v_declName_1196_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
lean_inc(v_declName_1196_);
lean_inc_ref(v_env_1195_);
v___x_1202_ = lean_is_reserved_name(v_env_1195_, v_declName_1196_);
v___y_1198_ = v___x_1202_;
goto v___jp_1197_;
}
else
{
v___y_1198_ = v___x_1201_;
goto v___jp_1197_;
}
v___jp_1197_:
{
if (v___y_1198_ == 0)
{
uint8_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 1;
v___x_1200_ = l_Lean_Environment_contains(v_env_1195_, v_declName_1196_, v___x_1199_);
return v___x_1200_;
}
else
{
lean_dec(v_declName_1196_);
lean_dec_ref(v_env_1195_);
return v___y_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1203_, lean_object* v_declName_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1203_, v_declName_1204_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1207_, lean_object* v_decl_1208_, lean_object* v_ref_1209_){
_start:
{
lean_object* v_defValue_1211_; lean_object* v_descr_1212_; lean_object* v_deprecation_x3f_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_defValue_1211_ = lean_ctor_get(v_decl_1208_, 0);
v_descr_1212_ = lean_ctor_get(v_decl_1208_, 1);
v_deprecation_x3f_1213_ = lean_ctor_get(v_decl_1208_, 2);
v___x_1214_ = lean_alloc_ctor(1, 0, 1);
v___x_1215_ = lean_unbox(v_defValue_1211_);
lean_ctor_set_uint8(v___x_1214_, 0, v___x_1215_);
lean_inc(v_deprecation_x3f_1213_);
lean_inc_ref(v_descr_1212_);
lean_inc_n(v_name_1207_, 2);
v___x_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1216_, 0, v_name_1207_);
lean_ctor_set(v___x_1216_, 1, v_ref_1209_);
lean_ctor_set(v___x_1216_, 2, v___x_1214_);
lean_ctor_set(v___x_1216_, 3, v_descr_1212_);
lean_ctor_set(v___x_1216_, 4, v_deprecation_x3f_1213_);
v___x_1217_ = lean_register_option(v_name_1207_, v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1226_);
v___x_1219_ = v___x_1217_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v___x_1217_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
lean_inc(v_defValue_1211_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_name_1207_);
lean_ctor_set(v___x_1221_, 1, v_defValue_1211_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_name_1207_);
v_a_1227_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1217_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1217_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1235_, lean_object* v_decl_1236_, lean_object* v_ref_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1235_, v_decl_1236_, v_ref_1237_);
lean_dec_ref(v_decl_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1259_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1260_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1261_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1258_, v___x_1259_, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1283_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1284_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1285_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1282_, v___x_1283_, v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1288_, lean_object* v_opt_1289_){
_start:
{
lean_object* v_name_1290_; lean_object* v_defValue_1291_; lean_object* v_map_1292_; lean_object* v___x_1293_; 
v_name_1290_ = lean_ctor_get(v_opt_1289_, 0);
v_defValue_1291_ = lean_ctor_get(v_opt_1289_, 1);
v_map_1292_ = lean_ctor_get(v_opts_1288_, 0);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1292_, v_name_1290_);
if (lean_obj_tag(v___x_1293_) == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_unbox(v_defValue_1291_);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; 
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1295_);
lean_dec_ref_known(v___x_1293_, 1);
if (lean_obj_tag(v_val_1295_) == 1)
{
uint8_t v_v_1296_; 
v_v_1296_ = lean_ctor_get_uint8(v_val_1295_, 0);
lean_dec_ref_known(v_val_1295_, 0);
return v_v_1296_;
}
else
{
uint8_t v___x_1297_; 
lean_dec(v_val_1295_);
v___x_1297_ = lean_unbox(v_defValue_1291_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1298_, lean_object* v_opt_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1298_, v_opt_1299_);
lean_dec_ref(v_opt_1299_);
lean_dec_ref(v_opts_1298_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1305_, lean_object* v_env_1306_, lean_object* v_as_1307_, size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_b_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_usize_dec_lt(v_i_1309_, v_sz_1308_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v_env_1306_);
lean_dec(v_declName_1305_);
lean_inc_ref(v_b_1310_);
return v_b_1310_;
}
else
{
lean_object* v_a_1312_; lean_object* v_toImport_1313_; lean_object* v_module_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_a_1312_ = lean_array_uget_borrowed(v_as_1307_, v_i_1309_);
v_toImport_1313_ = lean_ctor_get(v_a_1312_, 0);
v_module_1314_ = lean_ctor_get(v_toImport_1313_, 0);
v___x_1315_ = lean_box(0);
lean_inc(v_declName_1305_);
lean_inc(v_module_1314_);
v___x_1316_ = l_Lean_mkPrivateNameCore(v_module_1314_, v_declName_1305_);
lean_inc(v___x_1316_);
lean_inc_ref(v_env_1306_);
v___x_1317_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1306_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; 
lean_dec(v___x_1316_);
v___x_1318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_add(v_i_1309_, v___x_1319_);
v_i_1309_ = v___x_1320_;
v_b_1310_ = v___x_1318_;
goto _start;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_env_1306_);
lean_dec(v_declName_1305_);
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1316_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v___x_1315_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1325_, lean_object* v_env_1326_, lean_object* v_as_1327_, lean_object* v_sz_1328_, lean_object* v_i_1329_, lean_object* v_b_1330_){
_start:
{
size_t v_sz_boxed_1331_; size_t v_i_boxed_1332_; lean_object* v_res_1333_; 
v_sz_boxed_1331_ = lean_unbox_usize(v_sz_1328_);
lean_dec(v_sz_1328_);
v_i_boxed_1332_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_res_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1325_, v_env_1326_, v_as_1327_, v_sz_boxed_1331_, v_i_boxed_1332_, v_b_1330_);
lean_dec_ref(v_b_1330_);
lean_dec_ref(v_as_1327_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1334_, lean_object* v_opts_1335_, lean_object* v_declName_1336_){
_start:
{
uint8_t v_isExporting_1352_; 
v_isExporting_1352_ = lean_ctor_get_uint8(v_env_1334_, sizeof(void*)*13);
if (v_isExporting_1352_ == 0)
{
goto v___jp_1337_;
}
else
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1354_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1335_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_dec(v_declName_1336_);
lean_dec_ref(v_env_1334_);
v___x_1355_ = lean_box(0);
return v___x_1355_;
}
else
{
goto v___jp_1337_;
}
}
v___jp_1337_:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
lean_inc(v_declName_1336_);
v___x_1338_ = l_Lean_mkPrivateName(v_env_1334_, v_declName_1336_);
lean_inc(v___x_1338_);
lean_inc_ref(v_env_1334_);
v___x_1339_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1334_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; uint8_t v_isModule_1341_; 
lean_dec(v___x_1338_);
v___x_1340_ = l_Lean_Environment_header(v_env_1334_);
v_isModule_1341_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*7 + 4);
if (v_isModule_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v___x_1340_);
lean_dec(v_declName_1336_);
lean_dec_ref(v_env_1334_);
v___x_1342_ = lean_box(0);
return v___x_1342_;
}
else
{
lean_object* v_importAllModules_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; size_t v_sz_1346_; size_t v___x_1347_; lean_object* v___x_1348_; lean_object* v_fst_1349_; 
v_importAllModules_1343_ = lean_ctor_get(v___x_1340_, 5);
lean_inc_ref(v_importAllModules_1343_);
lean_dec_ref(v___x_1340_);
v___x_1344_ = lean_box(0);
v___x_1345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1346_ = lean_array_size(v_importAllModules_1343_);
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1336_, v_env_1334_, v_importAllModules_1343_, v_sz_1346_, v___x_1347_, v___x_1345_);
lean_dec_ref(v_importAllModules_1343_);
v_fst_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_fst_1349_);
lean_dec_ref(v___x_1348_);
if (lean_obj_tag(v_fst_1349_) == 0)
{
return v___x_1344_;
}
else
{
lean_object* v_val_1350_; 
v_val_1350_ = lean_ctor_get(v_fst_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v_fst_1349_, 1);
return v_val_1350_;
}
}
}
else
{
lean_object* v___x_1351_; 
lean_dec(v_declName_1336_);
lean_dec_ref(v_env_1334_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1338_);
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1356_, lean_object* v_opts_1357_, lean_object* v_declName_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1356_, v_opts_1357_, v_declName_1358_);
lean_dec_ref(v_opts_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1360_, lean_object* v_opts_1361_, lean_object* v_ns_1362_, lean_object* v_id_1363_){
_start:
{
lean_object* v_resolvedId_1364_; uint8_t v___x_1365_; lean_object* v_resolvedIds_1366_; 
lean_inc(v_id_1363_);
v_resolvedId_1364_ = l_Lean_Name_append(v_ns_1362_, v_id_1363_);
v___x_1365_ = l_Lean_Name_isAtomic(v_id_1363_);
lean_dec(v_id_1363_);
lean_inc_ref(v_env_1360_);
v_resolvedIds_1366_ = l_Lean_getAliases(v_env_1360_, v_resolvedId_1364_, v___x_1365_);
if (v___x_1365_ == 0)
{
goto v___jp_1367_;
}
else
{
uint8_t v___x_1373_; 
lean_inc(v_resolvedId_1364_);
lean_inc_ref(v_env_1360_);
v___x_1373_ = l_Lean_isProtected(v_env_1360_, v_resolvedId_1364_);
if (v___x_1373_ == 0)
{
goto v___jp_1367_;
}
else
{
lean_dec(v_resolvedId_1364_);
lean_dec_ref(v_env_1360_);
return v_resolvedIds_1366_;
}
}
v___jp_1367_:
{
uint8_t v___x_1368_; 
lean_inc(v_resolvedId_1364_);
lean_inc_ref(v_env_1360_);
v___x_1368_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1360_, v_resolvedId_1364_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1360_, v_opts_1361_, v_resolvedId_1364_);
if (lean_obj_tag(v___x_1369_) == 1)
{
lean_object* v_val_1370_; lean_object* v___x_1371_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_val_1370_);
lean_ctor_set(v___x_1371_, 1, v_resolvedIds_1366_);
return v___x_1371_;
}
else
{
lean_dec(v___x_1369_);
return v_resolvedIds_1366_;
}
}
else
{
lean_object* v___x_1372_; 
lean_dec_ref(v_env_1360_);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_resolvedId_1364_);
lean_ctor_set(v___x_1372_, 1, v_resolvedIds_1366_);
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1374_, lean_object* v_opts_1375_, lean_object* v_ns_1376_, lean_object* v_id_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1374_, v_opts_1375_, v_ns_1376_, v_id_1377_);
lean_dec_ref(v_opts_1375_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1379_, lean_object* v_opts_1380_, lean_object* v_id_1381_, lean_object* v_x_1382_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 1)
{
lean_object* v_pre_1383_; lean_object* v___x_1384_; 
v_pre_1383_ = lean_ctor_get(v_x_1382_, 0);
lean_inc(v_pre_1383_);
lean_inc(v_id_1381_);
lean_inc_ref(v_env_1379_);
v___x_1384_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1379_, v_opts_1380_, v_x_1382_, v_id_1381_);
if (lean_obj_tag(v___x_1384_) == 0)
{
v_x_1382_ = v_pre_1383_;
goto _start;
}
else
{
lean_dec(v_pre_1383_);
lean_dec(v_id_1381_);
lean_dec_ref(v_env_1379_);
return v___x_1384_;
}
}
else
{
lean_object* v___x_1386_; 
lean_dec(v_x_1382_);
lean_dec(v_id_1381_);
lean_dec_ref(v_env_1379_);
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1387_, lean_object* v_opts_1388_, lean_object* v_id_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1387_, v_opts_1388_, v_id_1389_, v_x_1390_);
lean_dec_ref(v_opts_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1392_, lean_object* v_opts_1393_, lean_object* v_id_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = l_Lean_Name_isAtomic(v_id_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_resolvedId_1398_; uint8_t v___x_1399_; 
v___x_1396_ = l_Lean_rootNamespace;
v___x_1397_ = lean_box(0);
v_resolvedId_1398_ = l_Lean_Name_replacePrefix(v_id_1394_, v___x_1396_, v___x_1397_);
lean_inc(v_resolvedId_1398_);
lean_inc_ref(v_env_1392_);
v___x_1399_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1392_, v_resolvedId_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1392_, v_opts_1393_, v_resolvedId_1398_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v_env_1392_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_resolvedId_1398_);
return v___x_1401_;
}
}
else
{
lean_object* v___x_1402_; 
lean_dec(v_id_1394_);
lean_dec_ref(v_env_1392_);
v___x_1402_ = lean_box(0);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1403_, lean_object* v_opts_1404_, lean_object* v_id_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1403_, v_opts_1404_, v_id_1405_);
lean_dec_ref(v_opts_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1407_, lean_object* v_opts_1408_, lean_object* v_id_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_dec(v_id_1409_);
lean_dec_ref(v_env_1407_);
return v_x_1411_;
}
else
{
lean_object* v_head_1412_; 
v_head_1412_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_head_1412_);
if (lean_obj_tag(v_head_1412_) == 0)
{
lean_object* v_tail_1413_; lean_object* v_ns_1414_; lean_object* v_except_1415_; uint8_t v___x_1416_; 
v_tail_1413_ = lean_ctor_get(v_x_1410_, 1);
lean_inc(v_tail_1413_);
lean_dec_ref_known(v_x_1410_, 2);
v_ns_1414_ = lean_ctor_get(v_head_1412_, 0);
lean_inc(v_ns_1414_);
v_except_1415_ = lean_ctor_get(v_head_1412_, 1);
lean_inc(v_except_1415_);
lean_dec_ref_known(v_head_1412_, 2);
v___x_1416_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1409_, v_except_1415_);
lean_dec(v_except_1415_);
if (v___x_1416_ == 0)
{
lean_object* v_newResolvedIds_1417_; lean_object* v___x_1418_; 
lean_inc(v_id_1409_);
lean_inc_ref(v_env_1407_);
v_newResolvedIds_1417_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1407_, v_opts_1408_, v_ns_1414_, v_id_1409_);
v___x_1418_ = l_List_appendTR___redArg(v_newResolvedIds_1417_, v_x_1411_);
v_x_1410_ = v_tail_1413_;
v_x_1411_ = v___x_1418_;
goto _start;
}
else
{
lean_dec(v_ns_1414_);
v_x_1410_ = v_tail_1413_;
goto _start;
}
}
else
{
lean_object* v_tail_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1441_; 
v_tail_1421_ = lean_ctor_get(v_x_1410_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_x_1410_, 0);
lean_dec(v_unused_1442_);
v___x_1423_ = v_x_1410_;
v_isShared_1424_ = v_isSharedCheck_1441_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_tail_1421_);
lean_dec(v_x_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1441_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_id_1425_; lean_object* v_declName_1426_; uint8_t v___x_1427_; 
v_id_1425_ = lean_ctor_get(v_head_1412_, 0);
lean_inc(v_id_1425_);
v_declName_1426_ = lean_ctor_get(v_head_1412_, 1);
lean_inc(v_declName_1426_);
lean_dec_ref_known(v_head_1412_, 2);
v___x_1427_ = lean_name_eq(v_id_1425_, v_id_1409_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = l_Lean_Name_isPrefixOf(v_id_1425_, v_id_1409_);
if (v___x_1428_ == 0)
{
lean_dec(v_declName_1426_);
lean_dec(v_id_1425_);
lean_del_object(v___x_1423_);
v_x_1410_ = v_tail_1421_;
goto _start;
}
else
{
lean_object* v_candidate_1430_; uint8_t v___x_1431_; 
lean_inc(v_id_1409_);
v_candidate_1430_ = l_Lean_Name_replacePrefix(v_id_1409_, v_id_1425_, v_declName_1426_);
lean_dec(v_declName_1426_);
lean_dec(v_id_1425_);
lean_inc(v_candidate_1430_);
lean_inc_ref(v_env_1407_);
v___x_1431_ = l_Lean_Environment_contains(v_env_1407_, v_candidate_1430_, v___x_1428_);
if (v___x_1431_ == 0)
{
lean_dec(v_candidate_1430_);
lean_del_object(v___x_1423_);
v_x_1410_ = v_tail_1421_;
goto _start;
}
else
{
lean_object* v___x_1434_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_x_1411_);
lean_ctor_set(v___x_1423_, 0, v_candidate_1430_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_candidate_1430_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_x_1411_);
v___x_1434_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v_x_1410_ = v_tail_1421_;
v_x_1411_ = v___x_1434_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_id_1425_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_x_1411_);
lean_ctor_set(v___x_1423_, 0, v_declName_1426_);
v___x_1438_ = v___x_1423_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_declName_1426_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_x_1411_);
v___x_1438_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
v_x_1410_ = v_tail_1421_;
v_x_1411_ = v___x_1438_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1443_, lean_object* v_opts_1444_, lean_object* v_id_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1443_, v_opts_1444_, v_id_1445_, v_x_1446_, v_x_1447_);
lean_dec_ref(v_opts_1444_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1450_){
_start:
{
lean_object* v___f_1451_; lean_object* v___x_1452_; 
v___f_1451_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1452_ = l_List_eraseDupsBy___redArg(v___f_1451_, v_as_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
if (lean_obj_tag(v_a_1454_) == 0)
{
lean_object* v___x_1456_; 
lean_dec(v_projs_1453_);
v___x_1456_ = l_List_reverse___redArg(v_a_1455_);
return v___x_1456_;
}
else
{
lean_object* v_head_1457_; lean_object* v_tail_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1467_; 
v_head_1457_ = lean_ctor_get(v_a_1454_, 0);
v_tail_1458_ = lean_ctor_get(v_a_1454_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_a_1454_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1460_ = v_a_1454_;
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_tail_1458_);
lean_inc(v_head_1457_);
lean_dec(v_a_1454_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_inc(v_projs_1453_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_head_1457_);
lean_ctor_set(v___x_1462_, 1, v_projs_1453_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_a_1455_);
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1455_);
v___x_1464_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_a_1454_ = v_tail_1458_;
v_a_1455_ = v___x_1464_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1468_, lean_object* v_opts_1469_, lean_object* v_ns_1470_, lean_object* v_openDecls_1471_, lean_object* v_extractionResult_1472_, lean_object* v_id_1473_, lean_object* v_projs_1474_){
_start:
{
if (lean_obj_tag(v_id_1473_) == 1)
{
lean_object* v_pre_1475_; lean_object* v_str_1476_; lean_object* v_imported_1477_; lean_object* v_ctx_1478_; lean_object* v_scopes_1479_; lean_object* v___x_1480_; lean_object* v_id_1481_; lean_object* v___y_1483_; lean_object* v___x_1493_; lean_object* v___y_1495_; 
v_pre_1475_ = lean_ctor_get(v_id_1473_, 0);
lean_inc(v_pre_1475_);
v_str_1476_ = lean_ctor_get(v_id_1473_, 1);
lean_inc_ref(v_str_1476_);
v_imported_1477_ = lean_ctor_get(v_extractionResult_1472_, 1);
v_ctx_1478_ = lean_ctor_get(v_extractionResult_1472_, 2);
v_scopes_1479_ = lean_ctor_get(v_extractionResult_1472_, 3);
lean_inc(v_scopes_1479_);
lean_inc(v_ctx_1478_);
lean_inc(v_imported_1477_);
v___x_1480_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1480_, 0, v_id_1473_);
lean_ctor_set(v___x_1480_, 1, v_imported_1477_);
lean_ctor_set(v___x_1480_, 2, v_ctx_1478_);
lean_ctor_set(v___x_1480_, 3, v_scopes_1479_);
v_id_1481_ = l_Lean_MacroScopesView_review(v___x_1480_);
lean_inc(v_ns_1470_);
lean_inc(v_id_1481_);
lean_inc_ref(v_env_1468_);
v___x_1493_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1468_, v_opts_1469_, v_id_1481_, v_ns_1470_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1500_; 
lean_inc(v_id_1481_);
lean_inc_ref(v_env_1468_);
v___x_1500_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1468_, v_opts_1469_, v_id_1481_);
if (lean_obj_tag(v___x_1500_) == 0)
{
uint8_t v___x_1501_; 
lean_inc(v_id_1481_);
lean_inc_ref(v_env_1468_);
v___x_1501_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1468_, v_id_1481_);
if (v___x_1501_ == 0)
{
v___y_1495_ = v___x_1493_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1502_; 
lean_inc(v_id_1481_);
v___x_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_id_1481_);
lean_ctor_set(v___x_1502_, 1, v___x_1493_);
v___y_1495_ = v___x_1502_;
goto v___jp_1494_;
}
}
else
{
lean_object* v_val_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v_id_1481_);
lean_dec_ref(v_str_1476_);
lean_dec(v_pre_1475_);
lean_dec(v_openDecls_1471_);
lean_dec(v_ns_1470_);
lean_dec_ref(v_env_1468_);
v_val_1503_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v_val_1503_);
lean_ctor_set(v___x_1504_, 1, v_projs_1474_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
return v___x_1506_;
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_id_1481_);
lean_dec_ref(v_str_1476_);
lean_dec(v_pre_1475_);
lean_dec(v_openDecls_1471_);
lean_dec(v_ns_1470_);
lean_dec_ref(v_env_1468_);
v___x_1507_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1493_);
v___x_1508_ = lean_box(0);
v___x_1509_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1474_, v___x_1507_, v___x_1508_);
return v___x_1509_;
}
v___jp_1482_:
{
lean_object* v_resolvedIds_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v_resolvedIds_1487_; 
lean_inc(v_openDecls_1471_);
lean_inc(v_id_1481_);
lean_inc_ref_n(v_env_1468_, 2);
v_resolvedIds_1484_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1468_, v_opts_1469_, v_id_1481_, v_openDecls_1471_, v___y_1483_);
v___x_1485_ = l_Lean_Name_isAtomic(v_id_1481_);
v___x_1486_ = l_Lean_getAliases(v_env_1468_, v_id_1481_, v___x_1485_);
lean_dec(v_id_1481_);
v_resolvedIds_1487_ = l_List_appendTR___redArg(v___x_1486_, v_resolvedIds_1484_);
if (lean_obj_tag(v_resolvedIds_1487_) == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_str_1476_);
lean_ctor_set(v___x_1488_, 1, v_projs_1474_);
v_id_1473_ = v_pre_1475_;
v_projs_1474_ = v___x_1488_;
goto _start;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec_ref(v_str_1476_);
lean_dec(v_pre_1475_);
lean_dec(v_openDecls_1471_);
lean_dec(v_ns_1470_);
lean_dec_ref(v_env_1468_);
v___x_1490_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1487_);
v___x_1491_ = lean_box(0);
v___x_1492_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1474_, v___x_1490_, v___x_1491_);
return v___x_1492_;
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; 
lean_inc(v_id_1481_);
lean_inc_ref(v_env_1468_);
v___x_1496_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1468_, v_opts_1469_, v_id_1481_);
if (lean_obj_tag(v___x_1496_) == 1)
{
lean_object* v_val_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_val_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_val_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1493_);
v___x_1499_ = l_List_appendTR___redArg(v___x_1498_, v___y_1495_);
v___y_1483_ = v___x_1499_;
goto v___jp_1482_;
}
else
{
lean_dec(v___x_1496_);
lean_dec(v___x_1493_);
v___y_1483_ = v___y_1495_;
goto v___jp_1482_;
}
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_projs_1474_);
lean_dec(v_id_1473_);
lean_dec(v_openDecls_1471_);
lean_dec(v_ns_1470_);
lean_dec_ref(v_env_1468_);
v___x_1510_ = lean_box(0);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1511_, lean_object* v_opts_1512_, lean_object* v_ns_1513_, lean_object* v_openDecls_1514_, lean_object* v_extractionResult_1515_, lean_object* v_id_1516_, lean_object* v_projs_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1511_, v_opts_1512_, v_ns_1513_, v_openDecls_1514_, v_extractionResult_1515_, v_id_1516_, v_projs_1517_);
lean_dec_ref(v_extractionResult_1515_);
lean_dec_ref(v_opts_1512_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1519_, lean_object* v_opts_1520_, lean_object* v_ns_1521_, lean_object* v_openDecls_1522_, lean_object* v_id_1523_){
_start:
{
lean_object* v_extractionResult_1524_; lean_object* v_name_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_extractionResult_1524_ = l_Lean_extractMacroScopes(v_id_1523_);
v_name_1525_ = lean_ctor_get(v_extractionResult_1524_, 0);
lean_inc(v_name_1525_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1519_, v_opts_1520_, v_ns_1521_, v_openDecls_1522_, v_extractionResult_1524_, v_name_1525_, v___x_1526_);
lean_dec_ref(v_extractionResult_1524_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1528_, lean_object* v_opts_1529_, lean_object* v_ns_1530_, lean_object* v_openDecls_1531_, lean_object* v_id_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_ResolveName_resolveGlobalName(v_env_1528_, v_opts_1529_, v_ns_1530_, v_openDecls_1531_, v_id_1532_);
lean_dec_ref(v_opts_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_panic_fn_borrowed(v___x_1535_, v_msg_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1541_ = lean_unsigned_to_nat(9u);
v___x_1542_ = lean_unsigned_to_nat(230u);
v___x_1543_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1544_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1545_ = l_mkPanicMessageWithDecl(v___x_1544_, v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1546_, lean_object* v_n_1547_, lean_object* v_ns_1548_){
_start:
{
switch(lean_obj_tag(v_ns_1548_))
{
case 1:
{
lean_object* v_pre_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_pre_1549_ = lean_ctor_get(v_ns_1548_, 0);
lean_inc(v_pre_1549_);
lean_inc(v_n_1547_);
v___x_1550_ = l_Lean_Name_append(v_ns_1548_, v_n_1547_);
lean_inc_ref(v_env_1546_);
v___x_1551_ = l_Lean_Environment_isNamespace(v_env_1546_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_dec(v___x_1550_);
v_ns_1548_ = v_pre_1549_;
goto _start;
}
else
{
lean_object* v___x_1553_; 
lean_dec(v_pre_1549_);
lean_dec(v_n_1547_);
lean_dec_ref(v_env_1546_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1550_);
return v___x_1553_;
}
}
case 0:
{
lean_object* v___x_1554_; lean_object* v_n_1555_; uint8_t v___x_1556_; 
v___x_1554_ = l_Lean_rootNamespace;
v_n_1555_ = l_Lean_Name_replacePrefix(v_n_1547_, v___x_1554_, v_ns_1548_);
v___x_1556_ = l_Lean_Environment_isNamespace(v_env_1546_, v_n_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_dec(v_n_1555_);
v___x_1557_ = lean_box(0);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_n_1555_);
return v___x_1558_;
}
}
default: 
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v_ns_1548_);
lean_dec(v_n_1547_);
lean_dec_ref(v_env_1546_);
v___x_1559_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1560_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1559_);
return v___x_1560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1561_, lean_object* v_n_1562_, lean_object* v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1563_) == 0)
{
lean_object* v___x_1564_; 
lean_dec(v_n_1562_);
lean_dec_ref(v_env_1561_);
v___x_1564_ = lean_box(0);
return v___x_1564_;
}
else
{
lean_object* v_head_1565_; 
v_head_1565_ = lean_ctor_get(v_x_1563_, 0);
if (lean_obj_tag(v_head_1565_) == 0)
{
lean_object* v_tail_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1583_; 
lean_inc_ref(v_head_1565_);
v_tail_1566_ = lean_ctor_get(v_x_1563_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1563_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_x_1563_, 0);
lean_dec(v_unused_1584_);
v___x_1568_ = v_x_1563_;
v_isShared_1569_ = v_isSharedCheck_1583_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_tail_1566_);
lean_dec(v_x_1563_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1583_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_ns_1570_; lean_object* v_except_1571_; lean_object* v___x_1572_; uint8_t v___y_1574_; uint8_t v___x_1580_; 
v_ns_1570_ = lean_ctor_get(v_head_1565_, 0);
lean_inc(v_ns_1570_);
v_except_1571_ = lean_ctor_get(v_head_1565_, 1);
lean_inc(v_except_1571_);
lean_dec_ref_known(v_head_1565_, 2);
lean_inc(v_n_1562_);
v___x_1572_ = l_Lean_Name_append(v_ns_1570_, v_n_1562_);
lean_inc_ref(v_env_1561_);
v___x_1580_ = l_Lean_Environment_isNamespace(v_env_1561_, v___x_1572_);
if (v___x_1580_ == 0)
{
lean_dec(v_except_1571_);
v___y_1574_ = v___x_1580_;
goto v___jp_1573_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1562_, v_except_1571_);
lean_dec(v_except_1571_);
if (v___x_1581_ == 0)
{
v___y_1574_ = v___x_1580_;
goto v___jp_1573_;
}
else
{
lean_dec(v___x_1572_);
lean_del_object(v___x_1568_);
v_x_1563_ = v_tail_1566_;
goto _start;
}
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
lean_dec(v___x_1572_);
lean_del_object(v___x_1568_);
v_x_1563_ = v_tail_1566_;
goto _start;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1561_, v_n_1562_, v_tail_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1576_);
lean_ctor_set(v___x_1568_, 0, v___x_1572_);
v___x_1578_ = v___x_1568_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1572_);
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
}
else
{
lean_object* v_tail_1585_; 
v_tail_1585_ = lean_ctor_get(v_x_1563_, 1);
lean_inc(v_tail_1585_);
lean_dec_ref_known(v_x_1563_, 2);
v_x_1563_ = v_tail_1585_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1587_, lean_object* v_ns_1588_, lean_object* v_openDecls_1589_, lean_object* v_id_1590_){
_start:
{
lean_object* v___x_1591_; 
lean_inc(v_id_1590_);
lean_inc_ref(v_env_1587_);
v___x_1591_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1587_, v_id_1590_, v_ns_1588_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1587_, v_id_1590_, v_openDecls_1589_);
return v___x_1592_;
}
else
{
lean_object* v_val_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_val_1593_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1594_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1587_, v_id_1590_, v_openDecls_1589_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_val_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1596_, lean_object* v_inst_1597_){
_start:
{
lean_object* v_getCurrNamespace_1598_; lean_object* v_getOpenDecls_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1608_; 
v_getCurrNamespace_1598_ = lean_ctor_get(v_inst_1597_, 0);
v_getOpenDecls_1599_ = lean_ctor_get(v_inst_1597_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_inst_1597_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1601_ = v_inst_1597_;
v_isShared_1602_ = v_isSharedCheck_1608_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_getOpenDecls_1599_);
lean_inc(v_getCurrNamespace_1598_);
lean_dec(v_inst_1597_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1608_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_inc(v_inst_1596_);
v___x_1603_ = lean_apply_2(v_inst_1596_, lean_box(0), v_getCurrNamespace_1598_);
v___x_1604_ = lean_apply_2(v_inst_1596_, lean_box(0), v_getOpenDecls_1599_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v___x_1604_);
lean_ctor_set(v___x_1601_, 0, v___x_1603_);
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1609_, lean_object* v_n_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1611_, v_inst_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1620_, lean_object* v_toPure_1621_, lean_object* v_id_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, uint8_t v_____do__lift_1627_){
_start:
{
uint8_t v_isExporting_1631_; 
v_isExporting_1631_ = lean_ctor_get_uint8(v_____do__lift_1620_, sizeof(void*)*13);
if (v_isExporting_1631_ == 0)
{
lean_dec_ref(v_inst_1626_);
lean_dec(v_inst_1625_);
lean_dec_ref(v_inst_1624_);
lean_dec_ref(v_inst_1623_);
lean_dec(v_id_1622_);
goto v___jp_1628_;
}
else
{
uint8_t v___x_1632_; 
v___x_1632_ = l_Lean_isPrivateName(v_id_1622_);
if (v___x_1632_ == 0)
{
lean_dec_ref(v_inst_1626_);
lean_dec(v_inst_1625_);
lean_dec_ref(v_inst_1624_);
lean_dec_ref(v_inst_1623_);
lean_dec(v_id_1622_);
goto v___jp_1628_;
}
else
{
if (v_____do__lift_1627_ == 0)
{
lean_dec_ref(v_inst_1626_);
lean_dec(v_inst_1625_);
lean_dec_ref(v_inst_1624_);
lean_dec_ref(v_inst_1623_);
lean_dec(v_id_1622_);
goto v___jp_1628_;
}
else
{
lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_toPure_1621_);
v___x_1633_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1634_ = 0;
v___x_1635_ = l_Lean_MessageData_ofConstName(v_id_1622_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1633_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_logWarning___redArg(v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v___x_1638_);
return v___x_1639_;
}
}
}
v___jp_1628_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_apply_2(v_toPure_1621_, lean_box(0), v___x_1629_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1640_, lean_object* v_toPure_1641_, lean_object* v_id_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_____do__lift_1647_){
_start:
{
uint8_t v_____do__lift_199__boxed_1648_; lean_object* v_res_1649_; 
v_____do__lift_199__boxed_1648_ = lean_unbox(v_____do__lift_1647_);
v_res_1649_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1640_, v_toPure_1641_, v_id_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_, v_____do__lift_199__boxed_1648_);
lean_dec_ref(v_____do__lift_1640_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1650_, lean_object* v_id_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v___x_1656_, lean_object* v_toBind_1657_, lean_object* v_____do__lift_1658_){
_start:
{
lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_inc_ref(v_inst_1655_);
lean_inc_ref(v_inst_1652_);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1659_, 0, v_____do__lift_1658_);
lean_closure_set(v___f_1659_, 1, v_toPure_1650_);
lean_closure_set(v___f_1659_, 2, v_id_1651_);
lean_closure_set(v___f_1659_, 3, v_inst_1652_);
lean_closure_set(v___f_1659_, 4, v_inst_1653_);
lean_closure_set(v___f_1659_, 5, v_inst_1654_);
lean_closure_set(v___f_1659_, 6, v_inst_1655_);
v___x_1660_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1661_ = l_Lean_Option_getM___redArg(v_inst_1652_, v_inst_1655_, v___x_1656_, v___x_1660_);
v___x_1662_ = lean_apply_4(v_toBind_1657_, lean_box(0), lean_box(0), v___x_1661_, v___f_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_id_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v_toApplicative_1670_; lean_object* v_toBind_1671_; lean_object* v_getEnv_1672_; lean_object* v_toPure_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; 
v___x_1669_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1670_ = lean_ctor_get(v_inst_1663_, 0);
v_toBind_1671_ = lean_ctor_get(v_inst_1663_, 1);
lean_inc_n(v_toBind_1671_, 2);
v_getEnv_1672_ = lean_ctor_get(v_inst_1664_, 0);
lean_inc(v_getEnv_1672_);
lean_dec_ref(v_inst_1664_);
v_toPure_1673_ = lean_ctor_get(v_toApplicative_1670_, 1);
lean_inc(v_toPure_1673_);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1674_, 0, v_toPure_1673_);
lean_closure_set(v___f_1674_, 1, v_id_1668_);
lean_closure_set(v___f_1674_, 2, v_inst_1663_);
lean_closure_set(v___f_1674_, 3, v_inst_1666_);
lean_closure_set(v___f_1674_, 4, v_inst_1667_);
lean_closure_set(v___f_1674_, 5, v_inst_1665_);
lean_closure_set(v___f_1674_, 6, v___x_1669_);
lean_closure_set(v___f_1674_, 7, v_toBind_1671_);
v___x_1675_ = lean_apply_4(v_toBind_1671_, lean_box(0), lean_box(0), v_getEnv_1672_, v___f_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_id_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1677_, v_inst_1678_, v_inst_1679_, v_inst_1680_, v_inst_1681_, v_id_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1684_, lean_object* v_n_1685_, lean_object* v_toPure_1686_, uint8_t v___y_1687_, uint8_t v___x_1688_, lean_object* v_____r_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1684_, v_n_1685_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_box(v___y_1687_);
v___x_1692_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v_val_1693_; lean_object* v___x_1694_; uint8_t v_isModule_1695_; 
v_val_1693_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1694_ = l_Lean_Environment_header(v_env_1684_);
v_isModule_1695_ = lean_ctor_get_uint8(v___x_1694_, sizeof(void*)*7 + 4);
if (v_isModule_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v___x_1694_);
lean_dec(v_val_1693_);
v___x_1696_ = lean_box(v___x_1688_);
v___x_1697_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v_modules_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_modules_1698_ = lean_ctor_get(v___x_1694_, 3);
lean_inc_ref(v_modules_1698_);
lean_dec_ref(v___x_1694_);
v___x_1699_ = lean_array_get_size(v_modules_1698_);
v___x_1700_ = lean_nat_dec_lt(v_val_1693_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref(v_modules_1698_);
lean_dec(v_val_1693_);
v___x_1701_ = lean_box(v_isModule_1695_);
v___x_1702_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1701_);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v_toImport_1704_; uint8_t v_importAll_1705_; 
v___x_1703_ = lean_array_fget(v_modules_1698_, v_val_1693_);
lean_dec(v_val_1693_);
lean_dec_ref(v_modules_1698_);
v_toImport_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_toImport_1704_);
lean_dec(v___x_1703_);
v_importAll_1705_ = lean_ctor_get_uint8(v_toImport_1704_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1704_);
if (v_importAll_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_box(v_isModule_1695_);
v___x_1707_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1706_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_box(v___y_1687_);
v___x_1709_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1708_);
return v___x_1709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1710_, lean_object* v_n_1711_, lean_object* v_toPure_1712_, lean_object* v___y_1713_, lean_object* v___x_1714_, lean_object* v_____r_1715_){
_start:
{
uint8_t v___y_386__boxed_1716_; uint8_t v___x_387__boxed_1717_; lean_object* v_res_1718_; 
v___y_386__boxed_1716_ = lean_unbox(v___y_1713_);
v___x_387__boxed_1717_ = lean_unbox(v___x_1714_);
v_res_1718_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1710_, v_n_1711_, v_toPure_1712_, v___y_386__boxed_1716_, v___x_387__boxed_1717_, v_____r_1715_);
lean_dec(v_n_1711_);
lean_dec_ref(v_env_1710_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1719_, lean_object* v_n_1720_, lean_object* v_toPure_1721_, uint8_t v___x_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_toBind_1728_, uint8_t v___y_1729_, uint8_t v_____do__lift_1730_){
_start:
{
uint8_t v___y_1732_; uint8_t v_isExporting_1738_; 
v_isExporting_1738_ = lean_ctor_get_uint8(v_env_1719_, sizeof(void*)*13);
if (v_isExporting_1738_ == 0)
{
v___y_1732_ = v___y_1729_;
goto v___jp_1731_;
}
else
{
if (v_____do__lift_1730_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_toBind_1728_);
lean_dec(v_inst_1727_);
lean_dec_ref(v_inst_1726_);
lean_dec_ref(v_inst_1725_);
lean_dec_ref(v_inst_1724_);
lean_dec_ref(v_inst_1723_);
lean_dec(v_n_1720_);
lean_dec_ref(v_env_1719_);
v___x_1739_ = lean_box(v___x_1722_);
v___x_1740_ = lean_apply_2(v_toPure_1721_, lean_box(0), v___x_1739_);
return v___x_1740_;
}
else
{
v___y_1732_ = v___y_1729_;
goto v___jp_1731_;
}
}
v___jp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1733_ = lean_box(v___y_1732_);
v___x_1734_ = lean_box(v___x_1722_);
lean_inc(v_n_1720_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1735_, 0, v_env_1719_);
lean_closure_set(v___f_1735_, 1, v_n_1720_);
lean_closure_set(v___f_1735_, 2, v_toPure_1721_);
lean_closure_set(v___f_1735_, 3, v___x_1733_);
lean_closure_set(v___f_1735_, 4, v___x_1734_);
v___x_1736_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1723_, v_inst_1724_, v_inst_1725_, v_inst_1726_, v_inst_1727_, v_n_1720_);
v___x_1737_ = lean_apply_4(v_toBind_1728_, lean_box(0), lean_box(0), v___x_1736_, v___f_1735_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1741_, lean_object* v_n_1742_, lean_object* v_toPure_1743_, lean_object* v___x_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v_toBind_1750_, lean_object* v___y_1751_, lean_object* v_____do__lift_1752_){
_start:
{
uint8_t v___x_427__boxed_1753_; uint8_t v___y_433__boxed_1754_; uint8_t v_____do__lift_434__boxed_1755_; lean_object* v_res_1756_; 
v___x_427__boxed_1753_ = lean_unbox(v___x_1744_);
v___y_433__boxed_1754_ = lean_unbox(v___y_1751_);
v_____do__lift_434__boxed_1755_ = lean_unbox(v_____do__lift_1752_);
v_res_1756_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1741_, v_n_1742_, v_toPure_1743_, v___x_427__boxed_1753_, v_inst_1745_, v_inst_1746_, v_inst_1747_, v_inst_1748_, v_inst_1749_, v_toBind_1750_, v___y_433__boxed_1754_, v_____do__lift_434__boxed_1755_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1757_, lean_object* v_toPure_1758_, uint8_t v___x_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_toBind_1765_, uint8_t v___y_1766_, lean_object* v___x_1767_, lean_object* v_env_1768_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1769_ = lean_box(v___x_1759_);
v___x_1770_ = lean_box(v___y_1766_);
lean_inc(v_toBind_1765_);
lean_inc_ref(v_inst_1762_);
lean_inc_ref(v_inst_1760_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1771_, 0, v_env_1768_);
lean_closure_set(v___f_1771_, 1, v_n_1757_);
lean_closure_set(v___f_1771_, 2, v_toPure_1758_);
lean_closure_set(v___f_1771_, 3, v___x_1769_);
lean_closure_set(v___f_1771_, 4, v_inst_1760_);
lean_closure_set(v___f_1771_, 5, v_inst_1761_);
lean_closure_set(v___f_1771_, 6, v_inst_1762_);
lean_closure_set(v___f_1771_, 7, v_inst_1763_);
lean_closure_set(v___f_1771_, 8, v_inst_1764_);
lean_closure_set(v___f_1771_, 9, v_toBind_1765_);
lean_closure_set(v___f_1771_, 10, v___x_1770_);
v___x_1772_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1773_ = l_Lean_Option_getM___redArg(v_inst_1760_, v_inst_1762_, v___x_1767_, v___x_1772_);
v___x_1774_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1773_, v___f_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1775_, lean_object* v_toPure_1776_, lean_object* v___x_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_toBind_1783_, lean_object* v___y_1784_, lean_object* v___x_1785_, lean_object* v_env_1786_){
_start:
{
uint8_t v___x_469__boxed_1787_; uint8_t v___y_475__boxed_1788_; lean_object* v_res_1789_; 
v___x_469__boxed_1787_ = lean_unbox(v___x_1777_);
v___y_475__boxed_1788_ = lean_unbox(v___y_1784_);
v_res_1789_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1775_, v_toPure_1776_, v___x_469__boxed_1787_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_inst_1781_, v_inst_1782_, v_toBind_1783_, v___y_475__boxed_1788_, v___x_1785_, v_env_1786_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_n_1795_){
_start:
{
lean_object* v___x_1796_; uint8_t v___y_1798_; uint8_t v___x_1813_; 
v___x_1796_ = l_Lean_KVMap_instValueBool;
v___x_1813_ = l_Lean_isPrivateName(v_n_1795_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = 1;
v___y_1798_ = v___x_1814_;
goto v___jp_1797_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = 0;
v___y_1798_ = v___x_1815_;
goto v___jp_1797_;
}
v___jp_1797_:
{
if (v___y_1798_ == 0)
{
lean_object* v_toApplicative_1799_; lean_object* v_toBind_1800_; lean_object* v_toPure_1801_; lean_object* v_getEnv_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; 
v_toApplicative_1799_ = lean_ctor_get(v_inst_1792_, 0);
v_toBind_1800_ = lean_ctor_get(v_inst_1792_, 1);
lean_inc_n(v_toBind_1800_, 2);
v_toPure_1801_ = lean_ctor_get(v_toApplicative_1799_, 1);
lean_inc(v_toPure_1801_);
v_getEnv_1802_ = lean_ctor_get(v_inst_1793_, 0);
lean_inc(v_getEnv_1802_);
v___x_1803_ = 1;
v___x_1804_ = lean_box(v___x_1803_);
v___x_1805_ = lean_box(v___y_1798_);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1806_, 0, v_n_1795_);
lean_closure_set(v___f_1806_, 1, v_toPure_1801_);
lean_closure_set(v___f_1806_, 2, v___x_1804_);
lean_closure_set(v___f_1806_, 3, v_inst_1792_);
lean_closure_set(v___f_1806_, 4, v_inst_1793_);
lean_closure_set(v___f_1806_, 5, v_inst_1794_);
lean_closure_set(v___f_1806_, 6, v_inst_1790_);
lean_closure_set(v___f_1806_, 7, v_inst_1791_);
lean_closure_set(v___f_1806_, 8, v_toBind_1800_);
lean_closure_set(v___f_1806_, 9, v___x_1805_);
lean_closure_set(v___f_1806_, 10, v___x_1796_);
v___x_1807_ = lean_apply_4(v_toBind_1800_, lean_box(0), lean_box(0), v_getEnv_1802_, v___f_1806_);
return v___x_1807_;
}
else
{
lean_object* v_toApplicative_1808_; lean_object* v_toPure_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_toApplicative_1808_ = lean_ctor_get(v_inst_1792_, 0);
lean_inc_ref(v_toApplicative_1808_);
lean_dec(v_n_1795_);
lean_dec_ref(v_inst_1794_);
lean_dec_ref(v_inst_1793_);
lean_dec_ref(v_inst_1792_);
lean_dec(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
v_toPure_1809_ = lean_ctor_get(v_toApplicative_1808_, 1);
lean_inc(v_toPure_1809_);
lean_dec_ref(v_toApplicative_1808_);
v___x_1810_ = 0;
v___x_1811_ = lean_box(v___x_1810_);
v___x_1812_ = lean_apply_2(v_toPure_1809_, lean_box(0), v___x_1811_);
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_n_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1817_, v_inst_1818_, v_inst_1819_, v_inst_1820_, v_inst_1821_, v_n_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1824_){
_start:
{
lean_object* v_fst_1825_; uint8_t v___x_1826_; 
v_fst_1825_ = lean_ctor_get(v_x_1824_, 0);
v___x_1826_ = l_Lean_isPrivateName(v_fst_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1827_);
lean_dec_ref(v_x_1827_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1830_, lean_object* v_res_1831_, lean_object* v_____r_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_apply_2(v_toPure_1830_, lean_box(0), v_res_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1834_, lean_object* v_toPure_1835_, lean_object* v_res_1836_, lean_object* v___f_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_toBind_1843_, lean_object* v___f_1844_, lean_object* v_____do__lift_1845_){
_start:
{
if (v_enableLog_1834_ == 0)
{
lean_object* v___x_1846_; 
lean_dec(v___f_1844_);
lean_dec(v_toBind_1843_);
lean_dec(v_inst_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_inst_1840_);
lean_dec_ref(v_inst_1839_);
lean_dec_ref(v_inst_1838_);
lean_dec_ref(v___f_1837_);
v___x_1846_ = lean_apply_2(v_toPure_1835_, lean_box(0), v_res_1836_);
return v___x_1846_;
}
else
{
uint8_t v_isExporting_1847_; 
v_isExporting_1847_ = lean_ctor_get_uint8(v_____do__lift_1845_, sizeof(void*)*13);
if (v_isExporting_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_dec(v___f_1844_);
lean_dec(v_toBind_1843_);
lean_dec(v_inst_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_inst_1840_);
lean_dec_ref(v_inst_1839_);
lean_dec_ref(v_inst_1838_);
lean_dec_ref(v___f_1837_);
v___x_1848_ = lean_apply_2(v_toPure_1835_, lean_box(0), v_res_1836_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; 
lean_inc(v_res_1836_);
v___x_1849_ = l_List_find_x3f___redArg(v___f_1837_, v_res_1836_);
if (lean_obj_tag(v___x_1849_) == 1)
{
lean_object* v_val_1850_; lean_object* v_fst_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v_res_1836_);
lean_dec(v_toPure_1835_);
v_val_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v_fst_1851_ = lean_ctor_get(v_val_1850_, 0);
lean_inc(v_fst_1851_);
lean_dec(v_val_1850_);
v___x_1852_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1838_, v_inst_1839_, v_inst_1840_, v_inst_1841_, v_inst_1842_, v_fst_1851_);
v___x_1853_ = lean_apply_4(v_toBind_1843_, lean_box(0), lean_box(0), v___x_1852_, v___f_1844_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; 
lean_dec(v___x_1849_);
lean_dec(v___f_1844_);
lean_dec(v_toBind_1843_);
lean_dec(v_inst_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_inst_1840_);
lean_dec_ref(v_inst_1839_);
lean_dec_ref(v_inst_1838_);
v___x_1854_ = lean_apply_2(v_toPure_1835_, lean_box(0), v_res_1836_);
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1855_, lean_object* v_toPure_1856_, lean_object* v_res_1857_, lean_object* v___f_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_toBind_1864_, lean_object* v___f_1865_, lean_object* v_____do__lift_1866_){
_start:
{
uint8_t v_enableLog_boxed_1867_; lean_object* v_res_1868_; 
v_enableLog_boxed_1867_ = lean_unbox(v_enableLog_1855_);
v_res_1868_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1867_, v_toPure_1856_, v_res_1857_, v___f_1858_, v_inst_1859_, v_inst_1860_, v_inst_1861_, v_inst_1862_, v_inst_1863_, v_toBind_1864_, v___f_1865_, v_____do__lift_1866_);
lean_dec_ref(v_____do__lift_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1869_, lean_object* v_____do__lift_1870_, lean_object* v_____do__lift_1871_, lean_object* v_id_1872_, lean_object* v_toPure_1873_, uint8_t v_enableLog_1874_, lean_object* v___f_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_toBind_1881_, lean_object* v_getEnv_1882_, lean_object* v_____do__lift_1883_){
_start:
{
lean_object* v_res_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; lean_object* v___f_1887_; lean_object* v___x_1888_; 
v_res_1884_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1869_, v_____do__lift_1870_, v_____do__lift_1871_, v_____do__lift_1883_, v_id_1872_);
lean_inc(v_res_1884_);
lean_inc(v_toPure_1873_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1885_, 0, v_toPure_1873_);
lean_closure_set(v___f_1885_, 1, v_res_1884_);
v___x_1886_ = lean_box(v_enableLog_1874_);
lean_inc(v_toBind_1881_);
v___f_1887_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1887_, 0, v___x_1886_);
lean_closure_set(v___f_1887_, 1, v_toPure_1873_);
lean_closure_set(v___f_1887_, 2, v_res_1884_);
lean_closure_set(v___f_1887_, 3, v___f_1875_);
lean_closure_set(v___f_1887_, 4, v_inst_1876_);
lean_closure_set(v___f_1887_, 5, v_inst_1877_);
lean_closure_set(v___f_1887_, 6, v_inst_1878_);
lean_closure_set(v___f_1887_, 7, v_inst_1879_);
lean_closure_set(v___f_1887_, 8, v_inst_1880_);
lean_closure_set(v___f_1887_, 9, v_toBind_1881_);
lean_closure_set(v___f_1887_, 10, v___f_1885_);
v___x_1888_ = lean_apply_4(v_toBind_1881_, lean_box(0), lean_box(0), v_getEnv_1882_, v___f_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1889_, lean_object* v_____do__lift_1890_, lean_object* v_____do__lift_1891_, lean_object* v_id_1892_, lean_object* v_toPure_1893_, lean_object* v_enableLog_1894_, lean_object* v___f_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_toBind_1901_, lean_object* v_getEnv_1902_, lean_object* v_____do__lift_1903_){
_start:
{
uint8_t v_enableLog_boxed_1904_; lean_object* v_res_1905_; 
v_enableLog_boxed_1904_ = lean_unbox(v_enableLog_1894_);
v_res_1905_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1889_, v_____do__lift_1890_, v_____do__lift_1891_, v_id_1892_, v_toPure_1893_, v_enableLog_boxed_1904_, v___f_1895_, v_inst_1896_, v_inst_1897_, v_inst_1898_, v_inst_1899_, v_inst_1900_, v_toBind_1901_, v_getEnv_1902_, v_____do__lift_1903_);
lean_dec_ref(v_____do__lift_1890_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1906_, lean_object* v_____do__lift_1907_, lean_object* v_id_1908_, lean_object* v_toPure_1909_, uint8_t v_enableLog_1910_, lean_object* v___f_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v_toBind_1917_, lean_object* v_getEnv_1918_, lean_object* v_getOpenDecls_1919_, lean_object* v_____do__lift_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___f_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_box(v_enableLog_1910_);
lean_inc(v_toBind_1917_);
v___f_1922_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1922_, 0, v_____do__lift_1906_);
lean_closure_set(v___f_1922_, 1, v_____do__lift_1907_);
lean_closure_set(v___f_1922_, 2, v_____do__lift_1920_);
lean_closure_set(v___f_1922_, 3, v_id_1908_);
lean_closure_set(v___f_1922_, 4, v_toPure_1909_);
lean_closure_set(v___f_1922_, 5, v___x_1921_);
lean_closure_set(v___f_1922_, 6, v___f_1911_);
lean_closure_set(v___f_1922_, 7, v_inst_1912_);
lean_closure_set(v___f_1922_, 8, v_inst_1913_);
lean_closure_set(v___f_1922_, 9, v_inst_1914_);
lean_closure_set(v___f_1922_, 10, v_inst_1915_);
lean_closure_set(v___f_1922_, 11, v_inst_1916_);
lean_closure_set(v___f_1922_, 12, v_toBind_1917_);
lean_closure_set(v___f_1922_, 13, v_getEnv_1918_);
v___x_1923_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v_getOpenDecls_1919_, v___f_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1924_, lean_object* v_____do__lift_1925_, lean_object* v_id_1926_, lean_object* v_toPure_1927_, lean_object* v_enableLog_1928_, lean_object* v___f_1929_, lean_object* v_inst_1930_, lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_toBind_1935_, lean_object* v_getEnv_1936_, lean_object* v_getOpenDecls_1937_, lean_object* v_____do__lift_1938_){
_start:
{
uint8_t v_enableLog_boxed_1939_; lean_object* v_res_1940_; 
v_enableLog_boxed_1939_ = lean_unbox(v_enableLog_1928_);
v_res_1940_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1924_, v_____do__lift_1925_, v_id_1926_, v_toPure_1927_, v_enableLog_boxed_1939_, v___f_1929_, v_inst_1930_, v_inst_1931_, v_inst_1932_, v_inst_1933_, v_inst_1934_, v_toBind_1935_, v_getEnv_1936_, v_getOpenDecls_1937_, v_____do__lift_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1941_, lean_object* v_____do__lift_1942_, lean_object* v_id_1943_, lean_object* v_toPure_1944_, uint8_t v_enableLog_1945_, lean_object* v___f_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_toBind_1952_, lean_object* v_getEnv_1953_, lean_object* v_____do__lift_1954_){
_start:
{
lean_object* v_getCurrNamespace_1955_; lean_object* v_getOpenDecls_1956_; lean_object* v___x_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_getCurrNamespace_1955_ = lean_ctor_get(v_inst_1941_, 0);
lean_inc(v_getCurrNamespace_1955_);
v_getOpenDecls_1956_ = lean_ctor_get(v_inst_1941_, 1);
lean_inc(v_getOpenDecls_1956_);
lean_dec_ref(v_inst_1941_);
v___x_1957_ = lean_box(v_enableLog_1945_);
lean_inc(v_toBind_1952_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1958_, 0, v_____do__lift_1942_);
lean_closure_set(v___f_1958_, 1, v_____do__lift_1954_);
lean_closure_set(v___f_1958_, 2, v_id_1943_);
lean_closure_set(v___f_1958_, 3, v_toPure_1944_);
lean_closure_set(v___f_1958_, 4, v___x_1957_);
lean_closure_set(v___f_1958_, 5, v___f_1946_);
lean_closure_set(v___f_1958_, 6, v_inst_1947_);
lean_closure_set(v___f_1958_, 7, v_inst_1948_);
lean_closure_set(v___f_1958_, 8, v_inst_1949_);
lean_closure_set(v___f_1958_, 9, v_inst_1950_);
lean_closure_set(v___f_1958_, 10, v_inst_1951_);
lean_closure_set(v___f_1958_, 11, v_toBind_1952_);
lean_closure_set(v___f_1958_, 12, v_getEnv_1953_);
lean_closure_set(v___f_1958_, 13, v_getOpenDecls_1956_);
v___x_1959_ = lean_apply_4(v_toBind_1952_, lean_box(0), lean_box(0), v_getCurrNamespace_1955_, v___f_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1960_, lean_object* v_____do__lift_1961_, lean_object* v_id_1962_, lean_object* v_toPure_1963_, lean_object* v_enableLog_1964_, lean_object* v___f_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_toBind_1971_, lean_object* v_getEnv_1972_, lean_object* v_____do__lift_1973_){
_start:
{
uint8_t v_enableLog_boxed_1974_; lean_object* v_res_1975_; 
v_enableLog_boxed_1974_ = lean_unbox(v_enableLog_1964_);
v_res_1975_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1960_, v_____do__lift_1961_, v_id_1962_, v_toPure_1963_, v_enableLog_boxed_1974_, v___f_1965_, v_inst_1966_, v_inst_1967_, v_inst_1968_, v_inst_1969_, v_inst_1970_, v_toBind_1971_, v_getEnv_1972_, v_____do__lift_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_id_1978_, lean_object* v_toPure_1979_, uint8_t v_enableLog_1980_, lean_object* v___f_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_toBind_1986_, lean_object* v_getEnv_1987_, lean_object* v_____do__lift_1988_){
_start:
{
lean_object* v_getOptions_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; 
v_getOptions_1989_ = lean_ctor_get(v_inst_1976_, 0);
lean_inc(v_getOptions_1989_);
v___x_1990_ = lean_box(v_enableLog_1980_);
lean_inc(v_toBind_1986_);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1991_, 0, v_inst_1977_);
lean_closure_set(v___f_1991_, 1, v_____do__lift_1988_);
lean_closure_set(v___f_1991_, 2, v_id_1978_);
lean_closure_set(v___f_1991_, 3, v_toPure_1979_);
lean_closure_set(v___f_1991_, 4, v___x_1990_);
lean_closure_set(v___f_1991_, 5, v___f_1981_);
lean_closure_set(v___f_1991_, 6, v_inst_1982_);
lean_closure_set(v___f_1991_, 7, v_inst_1983_);
lean_closure_set(v___f_1991_, 8, v_inst_1976_);
lean_closure_set(v___f_1991_, 9, v_inst_1984_);
lean_closure_set(v___f_1991_, 10, v_inst_1985_);
lean_closure_set(v___f_1991_, 11, v_toBind_1986_);
lean_closure_set(v___f_1991_, 12, v_getEnv_1987_);
v___x_1992_ = lean_apply_4(v_toBind_1986_, lean_box(0), lean_box(0), v_getOptions_1989_, v___f_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_id_1995_, lean_object* v_toPure_1996_, lean_object* v_enableLog_1997_, lean_object* v___f_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_toBind_2003_, lean_object* v_getEnv_2004_, lean_object* v_____do__lift_2005_){
_start:
{
uint8_t v_enableLog_boxed_2006_; lean_object* v_res_2007_; 
v_enableLog_boxed_2006_ = lean_unbox(v_enableLog_1997_);
v_res_2007_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1993_, v_inst_1994_, v_id_1995_, v_toPure_1996_, v_enableLog_boxed_2006_, v___f_1998_, v_inst_1999_, v_inst_2000_, v_inst_2001_, v_inst_2002_, v_toBind_2003_, v_getEnv_2004_, v_____do__lift_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_id_2015_, uint8_t v_enableLog_2016_){
_start:
{
lean_object* v_toApplicative_2017_; lean_object* v_toBind_2018_; lean_object* v_getEnv_2019_; lean_object* v_toPure_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; 
v_toApplicative_2017_ = lean_ctor_get(v_inst_2009_, 0);
v_toBind_2018_ = lean_ctor_get(v_inst_2009_, 1);
lean_inc_n(v_toBind_2018_, 2);
v_getEnv_2019_ = lean_ctor_get(v_inst_2011_, 0);
lean_inc_n(v_getEnv_2019_, 2);
v_toPure_2020_ = lean_ctor_get(v_toApplicative_2017_, 1);
lean_inc(v_toPure_2020_);
v___f_2021_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2022_ = lean_box(v_enableLog_2016_);
v___f_2023_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2023_, 0, v_inst_2012_);
lean_closure_set(v___f_2023_, 1, v_inst_2010_);
lean_closure_set(v___f_2023_, 2, v_id_2015_);
lean_closure_set(v___f_2023_, 3, v_toPure_2020_);
lean_closure_set(v___f_2023_, 4, v___x_2022_);
lean_closure_set(v___f_2023_, 5, v___f_2021_);
lean_closure_set(v___f_2023_, 6, v_inst_2009_);
lean_closure_set(v___f_2023_, 7, v_inst_2011_);
lean_closure_set(v___f_2023_, 8, v_inst_2013_);
lean_closure_set(v___f_2023_, 9, v_inst_2014_);
lean_closure_set(v___f_2023_, 10, v_toBind_2018_);
lean_closure_set(v___f_2023_, 11, v_getEnv_2019_);
v___x_2024_ = lean_apply_4(v_toBind_2018_, lean_box(0), lean_box(0), v_getEnv_2019_, v___f_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_id_2031_, lean_object* v_enableLog_2032_){
_start:
{
uint8_t v_enableLog_boxed_2033_; lean_object* v_res_2034_; 
v_enableLog_boxed_2033_ = lean_unbox(v_enableLog_2032_);
v_res_2034_ = l_Lean_resolveGlobalName___redArg(v_inst_2025_, v_inst_2026_, v_inst_2027_, v_inst_2028_, v_inst_2029_, v_inst_2030_, v_id_2031_, v_enableLog_boxed_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_id_2042_, uint8_t v_enableLog_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_resolveGlobalName___redArg(v_inst_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_inst_2040_, v_inst_2041_, v_id_2042_, v_enableLog_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_id_2052_, lean_object* v_enableLog_2053_){
_start:
{
uint8_t v_enableLog_boxed_2054_; lean_object* v_res_2055_; 
v_enableLog_boxed_2054_ = lean_unbox(v_enableLog_2053_);
v_res_2055_ = l_Lean_resolveGlobalName(v_m_2045_, v_inst_2046_, v_inst_2047_, v_inst_2048_, v_inst_2049_, v_inst_2050_, v_inst_2051_, v_id_2052_, v_enableLog_boxed_2054_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2056_, lean_object* v_nss_2057_, lean_object* v_____r_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_apply_2(v_toPure_2056_, lean_box(0), v_nss_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2062_, lean_object* v_____do__lift_2063_, lean_object* v_id_2064_, uint8_t v_allowEmpty_2065_, lean_object* v_toPure_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_toBind_2069_, lean_object* v_____do__lift_2070_){
_start:
{
lean_object* v_nss_2071_; 
lean_inc(v_id_2064_);
v_nss_2071_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2062_, v_____do__lift_2063_, v_____do__lift_2070_, v_id_2064_);
if (v_allowEmpty_2065_ == 0)
{
uint8_t v___x_2072_; 
v___x_2072_ = l_List_isEmpty___redArg(v_nss_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v_toBind_2069_);
lean_dec_ref(v_inst_2068_);
lean_dec_ref(v_inst_2067_);
lean_dec(v_id_2064_);
v___x_2073_ = lean_apply_2(v_toPure_2066_, lean_box(0), v_nss_2071_);
return v___x_2073_;
}
else
{
lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2074_, 0, v_toPure_2066_);
lean_closure_set(v___f_2074_, 1, v_nss_2071_);
v___x_2075_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2064_, v___x_2072_);
v___x_2077_ = lean_string_append(v___x_2075_, v___x_2076_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2079_ = lean_string_append(v___x_2077_, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___x_2081_ = l_Lean_MessageData_ofFormat(v___x_2080_);
v___x_2082_ = l_Lean_throwError___redArg(v_inst_2067_, v_inst_2068_, v___x_2081_);
v___x_2083_ = lean_apply_4(v_toBind_2069_, lean_box(0), lean_box(0), v___x_2082_, v___f_2074_);
return v___x_2083_;
}
}
else
{
lean_object* v___x_2084_; 
lean_dec(v_toBind_2069_);
lean_dec_ref(v_inst_2068_);
lean_dec_ref(v_inst_2067_);
lean_dec(v_id_2064_);
v___x_2084_ = lean_apply_2(v_toPure_2066_, lean_box(0), v_nss_2071_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2085_, lean_object* v_____do__lift_2086_, lean_object* v_id_2087_, lean_object* v_allowEmpty_2088_, lean_object* v_toPure_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_toBind_2092_, lean_object* v_____do__lift_2093_){
_start:
{
uint8_t v_allowEmpty_boxed_2094_; lean_object* v_res_2095_; 
v_allowEmpty_boxed_2094_ = lean_unbox(v_allowEmpty_2088_);
v_res_2095_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2085_, v_____do__lift_2086_, v_id_2087_, v_allowEmpty_boxed_2094_, v_toPure_2089_, v_inst_2090_, v_inst_2091_, v_toBind_2092_, v_____do__lift_2093_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2096_, lean_object* v_id_2097_, uint8_t v_allowEmpty_2098_, lean_object* v_toPure_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_toBind_2102_, lean_object* v_getOpenDecls_2103_, lean_object* v_____do__lift_2104_){
_start:
{
lean_object* v___x_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(v_allowEmpty_2098_);
lean_inc(v_toBind_2102_);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2106_, 0, v_____do__lift_2096_);
lean_closure_set(v___f_2106_, 1, v_____do__lift_2104_);
lean_closure_set(v___f_2106_, 2, v_id_2097_);
lean_closure_set(v___f_2106_, 3, v___x_2105_);
lean_closure_set(v___f_2106_, 4, v_toPure_2099_);
lean_closure_set(v___f_2106_, 5, v_inst_2100_);
lean_closure_set(v___f_2106_, 6, v_inst_2101_);
lean_closure_set(v___f_2106_, 7, v_toBind_2102_);
v___x_2107_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v_getOpenDecls_2103_, v___f_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2108_, lean_object* v_id_2109_, lean_object* v_allowEmpty_2110_, lean_object* v_toPure_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_toBind_2114_, lean_object* v_getOpenDecls_2115_, lean_object* v_____do__lift_2116_){
_start:
{
uint8_t v_allowEmpty_boxed_2117_; lean_object* v_res_2118_; 
v_allowEmpty_boxed_2117_ = lean_unbox(v_allowEmpty_2110_);
v_res_2118_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2108_, v_id_2109_, v_allowEmpty_boxed_2117_, v_toPure_2111_, v_inst_2112_, v_inst_2113_, v_toBind_2114_, v_getOpenDecls_2115_, v_____do__lift_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2119_, lean_object* v_id_2120_, uint8_t v_allowEmpty_2121_, lean_object* v_toPure_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_toBind_2125_, lean_object* v_____do__lift_2126_){
_start:
{
lean_object* v_getCurrNamespace_2127_; lean_object* v_getOpenDecls_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; 
v_getCurrNamespace_2127_ = lean_ctor_get(v_inst_2119_, 0);
lean_inc(v_getCurrNamespace_2127_);
v_getOpenDecls_2128_ = lean_ctor_get(v_inst_2119_, 1);
lean_inc(v_getOpenDecls_2128_);
lean_dec_ref(v_inst_2119_);
v___x_2129_ = lean_box(v_allowEmpty_2121_);
lean_inc(v_toBind_2125_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2130_, 0, v_____do__lift_2126_);
lean_closure_set(v___f_2130_, 1, v_id_2120_);
lean_closure_set(v___f_2130_, 2, v___x_2129_);
lean_closure_set(v___f_2130_, 3, v_toPure_2122_);
lean_closure_set(v___f_2130_, 4, v_inst_2123_);
lean_closure_set(v___f_2130_, 5, v_inst_2124_);
lean_closure_set(v___f_2130_, 6, v_toBind_2125_);
lean_closure_set(v___f_2130_, 7, v_getOpenDecls_2128_);
v___x_2131_ = lean_apply_4(v_toBind_2125_, lean_box(0), lean_box(0), v_getCurrNamespace_2127_, v___f_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2132_, lean_object* v_id_2133_, lean_object* v_allowEmpty_2134_, lean_object* v_toPure_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_toBind_2138_, lean_object* v_____do__lift_2139_){
_start:
{
uint8_t v_allowEmpty_boxed_2140_; lean_object* v_res_2141_; 
v_allowEmpty_boxed_2140_ = lean_unbox(v_allowEmpty_2134_);
v_res_2141_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2132_, v_id_2133_, v_allowEmpty_boxed_2140_, v_toPure_2135_, v_inst_2136_, v_inst_2137_, v_toBind_2138_, v_____do__lift_2139_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_id_2146_, uint8_t v_allowEmpty_2147_){
_start:
{
lean_object* v_toApplicative_2148_; lean_object* v_toBind_2149_; lean_object* v_getEnv_2150_; lean_object* v_toPure_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; 
v_toApplicative_2148_ = lean_ctor_get(v_inst_2142_, 0);
v_toBind_2149_ = lean_ctor_get(v_inst_2142_, 1);
lean_inc_n(v_toBind_2149_, 2);
v_getEnv_2150_ = lean_ctor_get(v_inst_2144_, 0);
lean_inc(v_getEnv_2150_);
lean_dec_ref(v_inst_2144_);
v_toPure_2151_ = lean_ctor_get(v_toApplicative_2148_, 1);
lean_inc(v_toPure_2151_);
v___x_2152_ = lean_box(v_allowEmpty_2147_);
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2153_, 0, v_inst_2143_);
lean_closure_set(v___f_2153_, 1, v_id_2146_);
lean_closure_set(v___f_2153_, 2, v___x_2152_);
lean_closure_set(v___f_2153_, 3, v_toPure_2151_);
lean_closure_set(v___f_2153_, 4, v_inst_2142_);
lean_closure_set(v___f_2153_, 5, v_inst_2145_);
lean_closure_set(v___f_2153_, 6, v_toBind_2149_);
v___x_2154_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v_getEnv_2150_, v___f_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_id_2159_, lean_object* v_allowEmpty_2160_){
_start:
{
uint8_t v_allowEmpty_boxed_2161_; lean_object* v_res_2162_; 
v_allowEmpty_boxed_2161_ = lean_unbox(v_allowEmpty_2160_);
v_res_2162_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2155_, v_inst_2156_, v_inst_2157_, v_inst_2158_, v_id_2159_, v_allowEmpty_boxed_2161_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_id_2168_, uint8_t v_allowEmpty_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2164_, v_inst_2165_, v_inst_2166_, v_inst_2167_, v_id_2168_, v_allowEmpty_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2171_, lean_object* v_inst_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_id_2176_, lean_object* v_allowEmpty_2177_){
_start:
{
uint8_t v_allowEmpty_boxed_2178_; lean_object* v_res_2179_; 
v_allowEmpty_boxed_2178_ = lean_unbox(v_allowEmpty_2177_);
v_res_2179_ = l_Lean_resolveNamespaceCore(v_m_2171_, v_inst_2172_, v_inst_2173_, v_inst_2174_, v_inst_2175_, v_id_2176_, v_allowEmpty_boxed_2178_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2180_){
_start:
{
if (lean_obj_tag(v_x_2180_) == 0)
{
lean_object* v_ns_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_ns_2181_ = lean_ctor_get(v_x_2180_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2180_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v_x_2180_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_ns_2181_);
lean_dec(v_x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set_tag(v___x_2183_, 1);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_ns_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v___x_2189_; 
lean_dec_ref(v_x_2180_);
v___x_2189_ = lean_box(0);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2190_, lean_object* v_withRef_2191_, lean_object* v___x_2192_, lean_object* v_oldRef_2193_){
_start:
{
lean_object* v_ref_2194_; lean_object* v___x_2195_; 
v_ref_2194_ = l_Lean_replaceRef(v_x_2190_, v_oldRef_2193_);
v___x_2195_ = lean_apply_3(v_withRef_2191_, lean_box(0), v_ref_2194_, v___x_2192_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2196_, lean_object* v_withRef_2197_, lean_object* v___x_2198_, lean_object* v_oldRef_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2196_, v_withRef_2197_, v___x_2198_, v_oldRef_2199_);
lean_dec(v_oldRef_2199_);
lean_dec(v_x_2196_);
return v_res_2200_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2208_ = l_Lean_MessageData_ofFormat(v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_x_2213_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 3)
{
lean_object* v_toApplicative_2214_; lean_object* v_toBind_2215_; lean_object* v_toPure_2216_; lean_object* v_toMonadRef_2217_; lean_object* v_val_2218_; lean_object* v_preresolved_2219_; lean_object* v___f_2220_; lean_object* v___x_2221_; lean_object* v_pre_2222_; uint8_t v___x_2223_; 
v_toApplicative_2214_ = lean_ctor_get(v_inst_2209_, 0);
v_toBind_2215_ = lean_ctor_get(v_inst_2209_, 1);
lean_inc(v_toBind_2215_);
v_toPure_2216_ = lean_ctor_get(v_toApplicative_2214_, 1);
v_toMonadRef_2217_ = lean_ctor_get(v_inst_2212_, 1);
v_val_2218_ = lean_ctor_get(v_x_2213_, 2);
v_preresolved_2219_ = lean_ctor_get(v_x_2213_, 3);
v___f_2220_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2221_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2219_);
v_pre_2222_ = l_List_filterMapTR_go___redArg(v___f_2220_, v_preresolved_2219_, v___x_2221_);
v___x_2223_ = l_List_isEmpty___redArg(v_pre_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
lean_inc(v_toPure_2216_);
lean_dec_ref_known(v_x_2213_, 4);
lean_dec(v_toBind_2215_);
lean_dec_ref(v_inst_2212_);
lean_dec_ref(v_inst_2211_);
lean_dec_ref(v_inst_2210_);
lean_dec_ref(v_inst_2209_);
v___x_2224_ = lean_apply_2(v_toPure_2216_, lean_box(0), v_pre_2222_);
return v___x_2224_;
}
else
{
lean_object* v_getRef_2225_; lean_object* v_withRef_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; 
lean_dec(v_pre_2222_);
v_getRef_2225_ = lean_ctor_get(v_toMonadRef_2217_, 0);
lean_inc(v_getRef_2225_);
v_withRef_2226_ = lean_ctor_get(v_toMonadRef_2217_, 1);
lean_inc(v_withRef_2226_);
v___x_2227_ = 0;
lean_inc(v_val_2218_);
v___x_2228_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2209_, v_inst_2210_, v_inst_2211_, v_inst_2212_, v_val_2218_, v___x_2227_);
v___f_2229_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2229_, 0, v_x_2213_);
lean_closure_set(v___f_2229_, 1, v_withRef_2226_);
lean_closure_set(v___f_2229_, 2, v___x_2228_);
v___x_2230_ = lean_apply_4(v_toBind_2215_, lean_box(0), lean_box(0), v_getRef_2225_, v___f_2229_);
return v___x_2230_;
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec_ref(v_inst_2211_);
lean_dec_ref(v_inst_2210_);
v___x_2231_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2232_ = l_Lean_throwErrorAt___redArg(v_inst_2209_, v_inst_2212_, v_x_2213_, v___x_2231_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_resolveNamespace___redArg(v_inst_2234_, v_inst_2235_, v_inst_2236_, v_inst_2237_, v_x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2242_, lean_object* v___f_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_toPure_2246_, lean_object* v_____do__lift_2247_){
_start:
{
if (lean_obj_tag(v_____do__lift_2247_) == 1)
{
lean_object* v_tail_2263_; 
v_tail_2263_ = lean_ctor_get(v_____do__lift_2247_, 1);
if (lean_obj_tag(v_tail_2263_) == 0)
{
lean_object* v_head_2264_; lean_object* v___x_2265_; 
lean_dec_ref(v_inst_2245_);
lean_dec_ref(v_inst_2244_);
lean_dec_ref(v___f_2243_);
v_head_2264_ = lean_ctor_get(v_____do__lift_2247_, 0);
lean_inc(v_head_2264_);
lean_dec_ref_known(v_____do__lift_2247_, 2);
v___x_2265_ = lean_apply_2(v_toPure_2246_, lean_box(0), v_head_2264_);
return v___x_2265_;
}
else
{
lean_dec(v_toPure_2246_);
goto v___jp_2248_;
}
}
else
{
lean_dec(v_toPure_2246_);
goto v___jp_2248_;
}
v___jp_2248_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2249_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2250_ = l_Lean_TSyntax_getId(v_id_2242_);
v___x_2251_ = 1;
v___x_2252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2250_, v___x_2251_);
v___x_2253_ = lean_string_append(v___x_2249_, v___x_2252_);
lean_dec_ref(v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2255_ = lean_string_append(v___x_2253_, v___x_2254_);
v___x_2256_ = l_List_toString___redArg(v___f_2243_, v_____do__lift_2247_);
v___x_2257_ = lean_string_append(v___x_2255_, v___x_2256_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_ofFormat(v___x_2260_);
v___x_2262_ = l_Lean_throwError___redArg(v_inst_2244_, v_inst_2245_, v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2266_, lean_object* v___f_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_toPure_2270_, lean_object* v_____do__lift_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2266_, v___f_2267_, v_inst_2268_, v_inst_2269_, v_toPure_2270_, v_____do__lift_2271_);
lean_dec(v_id_2266_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_id_2278_){
_start:
{
lean_object* v_toApplicative_2279_; lean_object* v_toBind_2280_; lean_object* v_toPure_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; 
v_toApplicative_2279_ = lean_ctor_get(v_inst_2274_, 0);
v_toBind_2280_ = lean_ctor_get(v_inst_2274_, 1);
lean_inc(v_toBind_2280_);
v_toPure_2281_ = lean_ctor_get(v_toApplicative_2279_, 1);
lean_inc(v_toPure_2281_);
v___f_2282_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2278_);
lean_inc_ref(v_inst_2277_);
lean_inc_ref(v_inst_2274_);
v___x_2283_ = l_Lean_resolveNamespace___redArg(v_inst_2274_, v_inst_2275_, v_inst_2276_, v_inst_2277_, v_id_2278_);
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2284_, 0, v_id_2278_);
lean_closure_set(v___f_2284_, 1, v___f_2282_);
lean_closure_set(v___f_2284_, 2, v_inst_2274_);
lean_closure_set(v___f_2284_, 3, v_inst_2277_);
lean_closure_set(v___f_2284_, 4, v_toPure_2281_);
v___x_2285_ = lean_apply_4(v_toBind_2280_, lean_box(0), lean_box(0), v___x_2283_, v___f_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_id_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2287_, v_inst_2288_, v_inst_2289_, v_inst_2290_, v_id_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2293_){
_start:
{
lean_object* v_snd_2294_; uint8_t v___x_2295_; 
v_snd_2294_ = lean_ctor_get(v_x_2293_, 1);
v___x_2295_ = l_List_isEmpty___redArg(v_snd_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2296_){
_start:
{
uint8_t v_res_2297_; lean_object* v_r_2298_; 
v_res_2297_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2296_);
lean_dec_ref(v_x_2296_);
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2299_){
_start:
{
lean_object* v_fst_2300_; 
v_fst_2300_ = lean_ctor_get(v_x_2299_, 0);
lean_inc(v_fst_2300_);
return v_fst_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2301_);
lean_dec_ref(v_x_2301_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2303_, lean_object* v_cs_2304_, lean_object* v_toPure_2305_, lean_object* v_____r_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = l_List_mapTR_loop___redArg(v___f_2303_, v_cs_2304_, v___x_2307_);
v___x_2309_ = lean_apply_2(v_toPure_2305_, lean_box(0), v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2310_, lean_object* v_____r_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_apply_1(v___f_2310_, v_____r_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2313_, lean_object* v_inst_2314_, lean_object* v_inst_2315_, lean_object* v_n_2316_, lean_object* v_toBind_2317_, lean_object* v___f_2318_, lean_object* v_____do__lift_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2313_, v_inst_2314_, v_inst_2315_, v_____do__lift_2319_, v_n_2316_);
v___x_2321_ = lean_apply_4(v_toBind_2317_, lean_box(0), lean_box(0), v___x_2320_, v___f_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_n_2327_, lean_object* v_cs_2328_){
_start:
{
lean_object* v_toApplicative_2329_; lean_object* v_toBind_2330_; lean_object* v_toPure_2331_; lean_object* v_toMonadRef_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v_cs_2336_; lean_object* v___f_2337_; uint8_t v___x_2338_; 
v_toApplicative_2329_ = lean_ctor_get(v_inst_2324_, 0);
v_toBind_2330_ = lean_ctor_get(v_inst_2324_, 1);
lean_inc(v_toBind_2330_);
v_toPure_2331_ = lean_ctor_get(v_toApplicative_2329_, 1);
v_toMonadRef_2332_ = lean_ctor_get(v_inst_2326_, 1);
v___f_2333_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2334_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2335_ = lean_box(0);
v_cs_2336_ = l_List_filterTR_loop___redArg(v___f_2333_, v_cs_2328_, v___x_2335_);
lean_inc(v_toPure_2331_);
lean_inc(v_cs_2336_);
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2337_, 0, v___f_2334_);
lean_closure_set(v___f_2337_, 1, v_cs_2336_);
lean_closure_set(v___f_2337_, 2, v_toPure_2331_);
v___x_2338_ = l_List_isEmpty___redArg(v_cs_2336_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_inc(v_toPure_2331_);
lean_dec_ref(v___f_2337_);
lean_dec(v_toBind_2330_);
lean_dec(v_n_2327_);
lean_dec_ref(v_inst_2326_);
lean_dec_ref(v_inst_2325_);
lean_dec_ref(v_inst_2324_);
v___x_2339_ = lean_box(0);
v___x_2340_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2334_, v_cs_2336_, v_toPure_2331_, v___x_2339_);
return v___x_2340_;
}
else
{
lean_object* v_getRef_2341_; lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; 
lean_dec(v_cs_2336_);
v_getRef_2341_ = lean_ctor_get(v_toMonadRef_2332_, 0);
lean_inc(v_getRef_2341_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2342_, 0, v___f_2337_);
lean_inc(v_toBind_2330_);
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2343_, 0, v_inst_2324_);
lean_closure_set(v___f_2343_, 1, v_inst_2325_);
lean_closure_set(v___f_2343_, 2, v_inst_2326_);
lean_closure_set(v___f_2343_, 3, v_n_2327_);
lean_closure_set(v___f_2343_, 4, v_toBind_2330_);
lean_closure_set(v___f_2343_, 5, v___f_2342_);
v___x_2344_ = lean_apply_4(v_toBind_2330_, lean_box(0), lean_box(0), v_getRef_2341_, v___f_2343_);
return v___x_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_n_2349_, lean_object* v_cs_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_filterFieldList___redArg(v_inst_2346_, v_inst_2347_, v_inst_2348_, v_n_2349_, v_cs_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_n_2355_, lean_object* v_cs_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_filterFieldList___redArg(v_inst_2352_, v_inst_2353_, v_inst_2354_, v_n_2355_, v_cs_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_n_2365_){
_start:
{
lean_object* v_toBind_2366_; lean_object* v___f_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_toBind_2366_ = lean_ctor_get(v_inst_2358_, 1);
lean_inc(v_toBind_2366_);
lean_inc(v_n_2365_);
lean_inc_ref(v_inst_2360_);
lean_inc_ref(v_inst_2358_);
v___f_2367_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2367_, 0, v_inst_2358_);
lean_closure_set(v___f_2367_, 1, v_inst_2360_);
lean_closure_set(v___f_2367_, 2, v_inst_2364_);
lean_closure_set(v___f_2367_, 3, v_n_2365_);
v___x_2368_ = 1;
v___x_2369_ = l_Lean_resolveGlobalName___redArg(v_inst_2358_, v_inst_2359_, v_inst_2360_, v_inst_2361_, v_inst_2362_, v_inst_2363_, v_n_2365_, v___x_2368_);
v___x_2370_ = lean_apply_4(v_toBind_2366_, lean_box(0), lean_box(0), v___x_2369_, v___f_2367_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_n_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2372_, v_inst_2373_, v_inst_2374_, v_inst_2375_, v_inst_2376_, v_inst_2377_, v_inst_2378_, v_n_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2381_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_box(0);
v___x_2383_ = l_Lean_mkConst(v_declName_2381_, v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2387_ = l_Lean_stringToMessageData(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_n_2394_, lean_object* v_cs_2395_){
_start:
{
lean_object* v_toApplicative_2396_; lean_object* v_toPure_2397_; lean_object* v___f_2398_; 
v_toApplicative_2396_ = lean_ctor_get(v_inst_2392_, 0);
v_toPure_2397_ = lean_ctor_get(v_toApplicative_2396_, 1);
v___f_2398_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2395_) == 1)
{
lean_object* v_tail_2412_; 
v_tail_2412_ = lean_ctor_get(v_cs_2395_, 1);
if (lean_obj_tag(v_tail_2412_) == 0)
{
lean_object* v_head_2413_; lean_object* v___x_2414_; 
lean_inc(v_toPure_2397_);
lean_dec(v_n_2394_);
lean_dec_ref(v_inst_2393_);
lean_dec_ref(v_inst_2392_);
v_head_2413_ = lean_ctor_get(v_cs_2395_, 0);
lean_inc(v_head_2413_);
lean_dec_ref_known(v_cs_2395_, 2);
v___x_2414_ = lean_apply_2(v_toPure_2397_, lean_box(0), v_head_2413_);
return v___x_2414_;
}
else
{
goto v___jp_2399_;
}
}
else
{
goto v___jp_2399_;
}
v___jp_2399_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2400_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2401_ = l_Lean_MessageData_ofName(v_n_2394_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_box(0);
v___x_2406_ = l_List_mapTR_loop___redArg(v___f_2398_, v_cs_2395_, v___x_2405_);
v___x_2407_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2408_ = l_List_mapTR_loop___redArg(v___x_2407_, v___x_2406_, v___x_2405_);
v___x_2409_ = l_Lean_MessageData_ofList(v___x_2408_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2404_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l_Lean_throwError___redArg(v_inst_2392_, v_inst_2393_, v___x_2410_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_n_2418_, lean_object* v_cs_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_ensureNoOverload___redArg(v_inst_2416_, v_inst_2417_, v_n_2418_, v_cs_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_n_2423_, lean_object* v_____do__lift_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_ensureNoOverload___redArg(v_inst_2421_, v_inst_2422_, v_n_2423_, v_____do__lift_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_n_2433_){
_start:
{
lean_object* v_toBind_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_toBind_2434_ = lean_ctor_get(v_inst_2426_, 1);
lean_inc(v_toBind_2434_);
lean_inc(v_n_2433_);
lean_inc_ref(v_inst_2432_);
lean_inc_ref(v_inst_2426_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2435_, 0, v_inst_2426_);
lean_closure_set(v___f_2435_, 1, v_inst_2432_);
lean_closure_set(v___f_2435_, 2, v_n_2433_);
v___x_2436_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2426_, v_inst_2427_, v_inst_2428_, v_inst_2429_, v_inst_2430_, v_inst_2431_, v_inst_2432_, v_n_2433_);
v___x_2437_ = lean_apply_4(v_toBind_2434_, lean_box(0), lean_box(0), v___x_2436_, v___f_2435_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_n_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2439_, v_inst_2440_, v_inst_2441_, v_inst_2442_, v_inst_2443_, v_inst_2444_, v_inst_2445_, v_n_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2448_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 1)
{
lean_object* v_fields_2449_; 
v_fields_2449_ = lean_ctor_get(v_x_2448_, 1);
if (lean_obj_tag(v_fields_2449_) == 0)
{
lean_object* v_n_2450_; lean_object* v___x_2451_; 
v_n_2450_ = lean_ctor_get(v_x_2448_, 0);
lean_inc(v_n_2450_);
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_n_2450_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_box(0);
return v___x_2452_;
}
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_box(0);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2454_);
lean_dec_ref(v_x_2454_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2456_, lean_object* v_withRef_2457_, lean_object* v___x_2458_, lean_object* v_oldRef_2459_){
_start:
{
lean_object* v_ref_2460_; lean_object* v___x_2461_; 
v_ref_2460_ = l_Lean_replaceRef(v_stx_2456_, v_oldRef_2459_);
v___x_2461_ = lean_apply_3(v_withRef_2457_, lean_box(0), v_ref_2460_, v___x_2458_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2462_, lean_object* v_withRef_2463_, lean_object* v___x_2464_, lean_object* v_oldRef_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2462_, v_withRef_2463_, v___x_2464_, v_oldRef_2465_);
lean_dec(v_oldRef_2465_);
lean_dec(v_stx_2462_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_stx_2470_, lean_object* v_k_2471_){
_start:
{
if (lean_obj_tag(v_stx_2470_) == 3)
{
lean_object* v_toApplicative_2472_; lean_object* v_toBind_2473_; lean_object* v_toPure_2474_; lean_object* v_toMonadRef_2475_; lean_object* v_val_2476_; lean_object* v_preresolved_2477_; lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v_pre_2480_; uint8_t v___x_2481_; 
v_toApplicative_2472_ = lean_ctor_get(v_inst_2468_, 0);
lean_inc_ref(v_toApplicative_2472_);
v_toBind_2473_ = lean_ctor_get(v_inst_2468_, 1);
lean_inc(v_toBind_2473_);
lean_dec_ref(v_inst_2468_);
v_toPure_2474_ = lean_ctor_get(v_toApplicative_2472_, 1);
lean_inc(v_toPure_2474_);
lean_dec_ref(v_toApplicative_2472_);
v_toMonadRef_2475_ = lean_ctor_get(v_inst_2469_, 1);
lean_inc_ref(v_toMonadRef_2475_);
lean_dec_ref(v_inst_2469_);
v_val_2476_ = lean_ctor_get(v_stx_2470_, 2);
v_preresolved_2477_ = lean_ctor_get(v_stx_2470_, 3);
v___f_2478_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2479_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2477_);
v_pre_2480_ = l_List_filterMapTR_go___redArg(v___f_2478_, v_preresolved_2477_, v___x_2479_);
v___x_2481_ = l_List_isEmpty___redArg(v_pre_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
lean_dec_ref(v_toMonadRef_2475_);
lean_dec(v_toBind_2473_);
lean_dec_ref_known(v_stx_2470_, 4);
lean_dec(v_k_2471_);
v___x_2482_ = lean_apply_2(v_toPure_2474_, lean_box(0), v_pre_2480_);
return v___x_2482_;
}
else
{
lean_object* v_getRef_2483_; lean_object* v_withRef_2484_; lean_object* v___x_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; 
lean_dec(v_pre_2480_);
lean_dec(v_toPure_2474_);
v_getRef_2483_ = lean_ctor_get(v_toMonadRef_2475_, 0);
lean_inc(v_getRef_2483_);
v_withRef_2484_ = lean_ctor_get(v_toMonadRef_2475_, 1);
lean_inc(v_withRef_2484_);
lean_dec_ref(v_toMonadRef_2475_);
lean_inc(v_val_2476_);
v___x_2485_ = lean_apply_1(v_k_2471_, v_val_2476_);
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2486_, 0, v_stx_2470_);
lean_closure_set(v___f_2486_, 1, v_withRef_2484_);
lean_closure_set(v___f_2486_, 2, v___x_2485_);
v___x_2487_ = lean_apply_4(v_toBind_2473_, lean_box(0), lean_box(0), v_getRef_2483_, v___f_2486_);
return v___x_2487_;
}
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_dec(v_k_2471_);
v___x_2488_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2489_ = l_Lean_throwErrorAt___redArg(v_inst_2468_, v_inst_2469_, v_stx_2470_, v___x_2488_);
return v___x_2489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_stx_2493_, lean_object* v_k_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2491_, v_inst_2492_, v_stx_2493_, v_k_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_stx_2503_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_inc_ref(v_inst_2502_);
lean_inc_ref(v_inst_2496_);
v___x_2504_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2504_, 0, lean_box(0));
lean_closure_set(v___x_2504_, 1, v_inst_2496_);
lean_closure_set(v___x_2504_, 2, v_inst_2497_);
lean_closure_set(v___x_2504_, 3, v_inst_2498_);
lean_closure_set(v___x_2504_, 4, v_inst_2499_);
lean_closure_set(v___x_2504_, 5, v_inst_2500_);
lean_closure_set(v___x_2504_, 6, v_inst_2501_);
lean_closure_set(v___x_2504_, 7, v_inst_2502_);
v___x_2505_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2496_, v_inst_2502_, v_stx_2503_, v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_stx_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_resolveGlobalConst___redArg(v_inst_2507_, v_inst_2508_, v_inst_2509_, v_inst_2510_, v_inst_2511_, v_inst_2512_, v_inst_2513_, v_stx_2514_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2517_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2518_ = lean_unsigned_to_nat(11u);
v___x_2519_ = lean_unsigned_to_nat(429u);
v___x_2520_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2521_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2522_ = l_mkPanicMessageWithDecl(v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_, v___x_2517_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_id_2528_, lean_object* v_cs_2529_){
_start:
{
if (lean_obj_tag(v_cs_2529_) == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec(v_id_2528_);
lean_dec_ref(v_inst_2527_);
v___x_2530_ = lean_box(0);
v___x_2531_ = l_instInhabitedOfMonad___redArg(v_inst_2526_, v___x_2530_);
v___x_2532_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2533_ = l_panic___redArg(v___x_2531_, v___x_2532_);
lean_dec(v___x_2531_);
return v___x_2533_;
}
else
{
lean_object* v_tail_2534_; 
v_tail_2534_ = lean_ctor_get(v_cs_2529_, 1);
if (lean_obj_tag(v_tail_2534_) == 0)
{
lean_object* v_toApplicative_2535_; lean_object* v_toPure_2536_; lean_object* v_head_2537_; lean_object* v___x_2538_; 
v_toApplicative_2535_ = lean_ctor_get(v_inst_2526_, 0);
lean_inc_ref(v_toApplicative_2535_);
lean_dec(v_id_2528_);
lean_dec_ref(v_inst_2527_);
lean_dec_ref(v_inst_2526_);
v_toPure_2536_ = lean_ctor_get(v_toApplicative_2535_, 1);
lean_inc(v_toPure_2536_);
lean_dec_ref(v_toApplicative_2535_);
v_head_2537_ = lean_ctor_get(v_cs_2529_, 0);
lean_inc(v_head_2537_);
lean_dec_ref_known(v_cs_2529_, 2);
v___x_2538_ = lean_apply_2(v_toPure_2536_, lean_box(0), v_head_2537_);
return v___x_2538_;
}
else
{
lean_object* v___f_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___f_2539_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2540_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2541_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2542_ = lean_box(0);
v___x_2543_ = 0;
lean_inc(v_id_2528_);
v___x_2544_ = l_Lean_Syntax_formatStx(v_id_2528_, v___x_2542_, v___x_2543_);
v___x_2545_ = l_Std_Format_defWidth;
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = l_Std_Format_pretty(v___x_2544_, v___x_2545_, v___x_2546_, v___x_2546_);
v___x_2548_ = lean_string_append(v___x_2541_, v___x_2547_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2550_ = lean_string_append(v___x_2548_, v___x_2549_);
v___x_2551_ = lean_box(0);
v___x_2552_ = l_List_mapTR_loop___redArg(v___f_2539_, v_cs_2529_, v___x_2551_);
v___x_2553_ = l_List_toString___redArg(v___x_2540_, v___x_2552_);
v___x_2554_ = lean_string_append(v___x_2550_, v___x_2553_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
v___x_2556_ = l_Lean_MessageData_ofFormat(v___x_2555_);
v___x_2557_ = l_Lean_throwErrorAt___redArg(v_inst_2526_, v_inst_2527_, v_id_2528_, v___x_2556_);
return v___x_2557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_id_2561_, lean_object* v_cs_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2559_, v_inst_2560_, v_id_2561_, v_cs_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_id_2566_, lean_object* v_____do__lift_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2564_, v_inst_2565_, v_id_2566_, v_____do__lift_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2569_, lean_object* v_inst_2570_, lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_id_2576_){
_start:
{
lean_object* v_toBind_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_toBind_2577_ = lean_ctor_get(v_inst_2569_, 1);
lean_inc(v_toBind_2577_);
lean_inc(v_id_2576_);
lean_inc_ref(v_inst_2575_);
lean_inc_ref(v_inst_2569_);
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2578_, 0, v_inst_2569_);
lean_closure_set(v___f_2578_, 1, v_inst_2575_);
lean_closure_set(v___f_2578_, 2, v_id_2576_);
v___x_2579_ = l_Lean_resolveGlobalConst___redArg(v_inst_2569_, v_inst_2570_, v_inst_2571_, v_inst_2572_, v_inst_2573_, v_inst_2574_, v_inst_2575_, v_id_2576_);
v___x_2580_ = lean_apply_4(v_toBind_2577_, lean_box(0), lean_box(0), v___x_2579_, v___f_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_id_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2582_, v_inst_2583_, v_inst_2584_, v_inst_2585_, v_inst_2586_, v_inst_2587_, v_inst_2588_, v_id_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2591_, lean_object* v___f_2592_, uint8_t v_globalDeclFoundNext_2593_, uint8_t v_globalDeclFound_2594_, lean_object* v_r_2595_){
_start:
{
lean_object* v___x_2596_; lean_object* v_r_2597_; uint8_t v___x_2598_; 
v___x_2596_ = lean_box(0);
v_r_2597_ = l_List_filterTR_loop___redArg(v___f_2591_, v_r_2595_, v___x_2596_);
v___x_2598_ = l_List_isEmpty___redArg(v_r_2597_);
lean_dec(v_r_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_box(v_globalDeclFoundNext_2593_);
v___x_2601_ = lean_apply_2(v___f_2592_, v___x_2599_, v___x_2600_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = lean_box(v_globalDeclFound_2594_);
v___x_2604_ = lean_apply_2(v___f_2592_, v___x_2602_, v___x_2603_);
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2605_, lean_object* v___f_2606_, lean_object* v_globalDeclFoundNext_2607_, lean_object* v_globalDeclFound_2608_, lean_object* v_r_2609_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2610_; uint8_t v_globalDeclFound_boxed_2611_; lean_object* v_res_2612_; 
v_globalDeclFoundNext_boxed_2610_ = lean_unbox(v_globalDeclFoundNext_2607_);
v_globalDeclFound_boxed_2611_ = lean_unbox(v_globalDeclFound_2608_);
v_res_2612_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2605_, v___f_2606_, v_globalDeclFoundNext_boxed_2610_, v_globalDeclFound_boxed_2611_, v_r_2609_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2613_, lean_object* v_projs_2614_, lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_inst_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_view_2621_, lean_object* v_findLocalDecl_x3f_2622_, lean_object* v_pre_2623_, lean_object* v_____r_2624_, lean_object* v_globalDeclFoundNext_2625_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2626_; lean_object* v_res_2627_; 
v_globalDeclFoundNext_boxed_2626_ = lean_unbox(v_globalDeclFoundNext_2625_);
v_res_2627_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2613_, v_projs_2614_, v_inst_2615_, v_inst_2616_, v_inst_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_, v_view_2621_, v_findLocalDecl_x3f_2622_, v_pre_2623_, v_____r_2624_, v_globalDeclFoundNext_boxed_2626_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_view_2634_, lean_object* v_findLocalDecl_x3f_2635_, lean_object* v_n_2636_, lean_object* v_projs_2637_, uint8_t v_globalDeclFound_2638_){
_start:
{
lean_object* v_toApplicative_2639_; lean_object* v_imported_2640_; lean_object* v_ctx_2641_; lean_object* v_scopes_2642_; lean_object* v_toBind_2643_; lean_object* v_toPure_2644_; lean_object* v___f_2645_; lean_object* v_givenNameView_2646_; uint8_t v___y_2648_; 
v_toApplicative_2639_ = lean_ctor_get(v_inst_2628_, 0);
v_imported_2640_ = lean_ctor_get(v_view_2634_, 1);
v_ctx_2641_ = lean_ctor_get(v_view_2634_, 2);
v_scopes_2642_ = lean_ctor_get(v_view_2634_, 3);
v_toBind_2643_ = lean_ctor_get(v_inst_2628_, 1);
v_toPure_2644_ = lean_ctor_get(v_toApplicative_2639_, 1);
v___f_2645_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2642_);
lean_inc(v_ctx_2641_);
lean_inc(v_imported_2640_);
lean_inc(v_n_2636_);
v_givenNameView_2646_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2646_, 0, v_n_2636_);
lean_ctor_set(v_givenNameView_2646_, 1, v_imported_2640_);
lean_ctor_set(v_givenNameView_2646_, 2, v_ctx_2641_);
lean_ctor_set(v_givenNameView_2646_, 3, v_scopes_2642_);
if (v_globalDeclFound_2638_ == 0)
{
v___y_2648_ = v_globalDeclFound_2638_;
goto v___jp_2647_;
}
else
{
uint8_t v___x_2684_; 
v___x_2684_ = l_List_isEmpty___redArg(v_projs_2637_);
if (v___x_2684_ == 0)
{
v___y_2648_ = v_globalDeclFound_2638_;
goto v___jp_2647_;
}
else
{
uint8_t v___x_2685_; 
v___x_2685_ = 0;
v___y_2648_ = v___x_2685_;
goto v___jp_2647_;
}
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_box(v___y_2648_);
lean_inc_ref(v_findLocalDecl_x3f_2635_);
lean_inc_ref(v_givenNameView_2646_);
v___x_2650_ = lean_apply_2(v_findLocalDecl_x3f_2635_, v_givenNameView_2646_, v___x_2649_);
if (lean_obj_tag(v___x_2650_) == 0)
{
if (lean_obj_tag(v_n_2636_) == 1)
{
lean_object* v_pre_2651_; lean_object* v_str_2652_; lean_object* v___f_2653_; 
v_pre_2651_ = lean_ctor_get(v_n_2636_, 0);
lean_inc_n(v_pre_2651_, 2);
v_str_2652_ = lean_ctor_get(v_n_2636_, 1);
lean_inc_ref_n(v_str_2652_, 2);
lean_dec_ref_known(v_n_2636_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2635_);
lean_inc_ref(v_view_2634_);
lean_inc(v_inst_2633_);
lean_inc_ref(v_inst_2632_);
lean_inc_ref(v_inst_2631_);
lean_inc_ref(v_inst_2630_);
lean_inc_ref(v_inst_2629_);
lean_inc_ref(v_inst_2628_);
lean_inc(v_projs_2637_);
v___f_2653_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2653_, 0, v_str_2652_);
lean_closure_set(v___f_2653_, 1, v_projs_2637_);
lean_closure_set(v___f_2653_, 2, v_inst_2628_);
lean_closure_set(v___f_2653_, 3, v_inst_2629_);
lean_closure_set(v___f_2653_, 4, v_inst_2630_);
lean_closure_set(v___f_2653_, 5, v_inst_2631_);
lean_closure_set(v___f_2653_, 6, v_inst_2632_);
lean_closure_set(v___f_2653_, 7, v_inst_2633_);
lean_closure_set(v___f_2653_, 8, v_view_2634_);
lean_closure_set(v___f_2653_, 9, v_findLocalDecl_x3f_2635_);
lean_closure_set(v___f_2653_, 10, v_pre_2651_);
if (v_globalDeclFound_2638_ == 0)
{
uint8_t v_globalDeclFoundNext_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_inc(v_toBind_2643_);
lean_dec_ref(v_str_2652_);
lean_dec(v_pre_2651_);
lean_dec(v_projs_2637_);
lean_dec_ref(v_findLocalDecl_x3f_2635_);
lean_dec_ref(v_view_2634_);
v_globalDeclFoundNext_2654_ = 1;
v___x_2655_ = lean_box(v_globalDeclFoundNext_2654_);
v___x_2656_ = lean_box(v_globalDeclFound_2638_);
v___f_2657_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2657_, 0, v___f_2645_);
lean_closure_set(v___f_2657_, 1, v___f_2653_);
lean_closure_set(v___f_2657_, 2, v___x_2655_);
lean_closure_set(v___f_2657_, 3, v___x_2656_);
v___x_2658_ = l_Lean_MacroScopesView_review(v_givenNameView_2646_);
v___x_2659_ = l_Lean_resolveGlobalName___redArg(v_inst_2628_, v_inst_2629_, v_inst_2630_, v_inst_2631_, v_inst_2632_, v_inst_2633_, v___x_2658_, v_globalDeclFound_2638_);
v___x_2660_ = lean_apply_4(v_toBind_2643_, lean_box(0), lean_box(0), v___x_2659_, v___f_2657_);
return v___x_2660_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec_ref(v___f_2653_);
lean_dec_ref_known(v_givenNameView_2646_, 4);
v___x_2661_ = lean_box(0);
v___x_2662_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2652_, v_projs_2637_, v_inst_2628_, v_inst_2629_, v_inst_2630_, v_inst_2631_, v_inst_2632_, v_inst_2633_, v_view_2634_, v_findLocalDecl_x3f_2635_, v_pre_2651_, v___x_2661_, v_globalDeclFound_2638_);
return v___x_2662_;
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_inc(v_toPure_2644_);
lean_dec_ref_known(v_givenNameView_2646_, 4);
lean_dec(v_projs_2637_);
lean_dec(v_n_2636_);
lean_dec_ref(v_findLocalDecl_x3f_2635_);
lean_dec_ref(v_view_2634_);
lean_dec(v_inst_2633_);
lean_dec_ref(v_inst_2632_);
lean_dec_ref(v_inst_2631_);
lean_dec_ref(v_inst_2630_);
lean_dec_ref(v_inst_2629_);
lean_dec_ref(v_inst_2628_);
v___x_2663_ = lean_box(0);
v___x_2664_ = lean_apply_2(v_toPure_2644_, lean_box(0), v___x_2663_);
return v___x_2664_;
}
}
else
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2681_; 
lean_inc(v_toPure_2644_);
lean_dec_ref_known(v_givenNameView_2646_, 4);
lean_dec(v_n_2636_);
lean_dec_ref(v_findLocalDecl_x3f_2635_);
lean_dec_ref(v_view_2634_);
lean_dec(v_inst_2633_);
lean_dec_ref(v_inst_2632_);
lean_dec_ref(v_inst_2631_);
lean_dec_ref(v_inst_2630_);
lean_dec_ref(v_inst_2629_);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_inst_2628_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; lean_object* v_unused_2683_; 
v_unused_2682_ = lean_ctor_get(v_inst_2628_, 1);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_inst_2628_, 0);
lean_dec(v_unused_2683_);
v___x_2666_ = v_inst_2628_;
v_isShared_2667_ = v_isSharedCheck_2681_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v_inst_2628_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2681_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_val_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2680_; 
v_val_2668_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2670_ = v___x_2650_;
v_isShared_2671_ = v_isSharedCheck_2680_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_val_2668_);
lean_dec(v___x_2650_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2680_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2672_ = l_Lean_LocalDecl_toExpr(v_val_2668_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v_projs_2637_);
lean_ctor_set(v___x_2666_, 0, v___x_2672_);
v___x_2674_ = v___x_2666_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_projs_2637_);
v___x_2674_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2674_);
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_apply_2(v_toPure_2644_, lean_box(0), v___x_2676_);
return v___x_2677_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2686_, lean_object* v_projs_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_view_2694_, lean_object* v_findLocalDecl_x3f_2695_, lean_object* v_pre_2696_, lean_object* v_____r_2697_, uint8_t v_globalDeclFoundNext_2698_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_str_2686_);
lean_ctor_set(v___x_2699_, 1, v_projs_2687_);
v___x_2700_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2688_, v_inst_2689_, v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_view_2694_, v_findLocalDecl_x3f_2695_, v_pre_2696_, v___x_2699_, v_globalDeclFoundNext_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_view_2707_, lean_object* v_findLocalDecl_x3f_2708_, lean_object* v_n_2709_, lean_object* v_projs_2710_, lean_object* v_globalDeclFound_2711_){
_start:
{
uint8_t v_globalDeclFound_boxed_2712_; lean_object* v_res_2713_; 
v_globalDeclFound_boxed_2712_ = lean_unbox(v_globalDeclFound_2711_);
v_res_2713_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2701_, v_inst_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_view_2707_, v_findLocalDecl_x3f_2708_, v_n_2709_, v_projs_2710_, v_globalDeclFound_boxed_2712_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_view_2721_, lean_object* v_findLocalDecl_x3f_2722_, lean_object* v_n_2723_, lean_object* v_projs_2724_, uint8_t v_globalDeclFound_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2715_, v_inst_2716_, v_inst_2717_, v_inst_2718_, v_inst_2719_, v_inst_2720_, v_view_2721_, v_findLocalDecl_x3f_2722_, v_n_2723_, v_projs_2724_, v_globalDeclFound_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_view_2734_, lean_object* v_findLocalDecl_x3f_2735_, lean_object* v_n_2736_, lean_object* v_projs_2737_, lean_object* v_globalDeclFound_2738_){
_start:
{
uint8_t v_globalDeclFound_boxed_2739_; lean_object* v_res_2740_; 
v_globalDeclFound_boxed_2739_ = lean_unbox(v_globalDeclFound_2738_);
v_res_2740_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2727_, v_inst_2728_, v_inst_2729_, v_inst_2730_, v_inst_2731_, v_inst_2732_, v_inst_2733_, v_view_2734_, v_findLocalDecl_x3f_2735_, v_n_2736_, v_projs_2737_, v_globalDeclFound_boxed_2739_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2741_, lean_object* v_givenNameView_2742_, lean_object* v_fullDeclName_2743_, lean_object* v_ns_2744_){
_start:
{
lean_object* v_name_2745_; lean_object* v_imported_2746_; lean_object* v_ctx_2747_; lean_object* v_scopes_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v_name_2745_ = lean_ctor_get(v_givenNameView_2742_, 0);
v_imported_2746_ = lean_ctor_get(v_givenNameView_2742_, 1);
v_ctx_2747_ = lean_ctor_get(v_givenNameView_2742_, 2);
v_scopes_2748_ = lean_ctor_get(v_givenNameView_2742_, 3);
lean_inc(v_name_2745_);
lean_inc(v_ns_2744_);
v___x_2749_ = l_Lean_Name_append(v_ns_2744_, v_name_2745_);
lean_inc(v_scopes_2748_);
lean_inc(v_ctx_2747_);
lean_inc(v_imported_2746_);
v___x_2750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v_imported_2746_);
lean_ctor_set(v___x_2750_, 2, v_ctx_2747_);
lean_ctor_set(v___x_2750_, 3, v_scopes_2748_);
v___x_2751_ = l_Lean_MacroScopesView_review(v___x_2750_);
v___x_2752_ = lean_name_eq(v___x_2751_, v_fullDeclName_2743_);
lean_dec(v___x_2751_);
if (v___x_2752_ == 0)
{
if (lean_obj_tag(v_ns_2744_) == 1)
{
lean_object* v_pre_2753_; 
v_pre_2753_ = lean_ctor_get(v_ns_2744_, 0);
lean_inc(v_pre_2753_);
lean_dec_ref_known(v_ns_2744_, 2);
v_ns_2744_ = v_pre_2753_;
goto _start;
}
else
{
lean_object* v___x_2755_; 
lean_dec(v_ns_2744_);
lean_dec_ref(v_givenNameView_2742_);
lean_dec_ref(v_localDecl_2741_);
v___x_2755_ = lean_box(0);
return v___x_2755_;
}
}
else
{
lean_object* v___x_2756_; 
lean_dec(v_ns_2744_);
lean_dec_ref(v_givenNameView_2742_);
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_localDecl_2741_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2757_, lean_object* v_givenNameView_2758_, lean_object* v_fullDeclName_2759_, lean_object* v_ns_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2757_, v_givenNameView_2758_, v_fullDeclName_2759_, v_ns_2760_);
lean_dec(v_fullDeclName_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2762_, lean_object* v_givenName_2763_){
_start:
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = l_Lean_LocalDecl_userName(v_localDecl_2762_);
v___x_2765_ = lean_name_eq(v___x_2764_, v_givenName_2763_);
lean_dec(v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
lean_dec_ref(v_localDecl_2762_);
v___x_2766_ = lean_box(0);
return v___x_2766_;
}
else
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_localDecl_2762_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2768_, lean_object* v_givenName_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2768_, v_givenName_2769_);
lean_dec(v_givenName_2769_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2771_, lean_object* v_givenName_2772_, uint8_t v_skipAuxDecl_2773_, lean_object* v___f_2774_, lean_object* v_auxDeclToFullName_2775_, lean_object* v_currNamespace_2776_, lean_object* v_givenNameView_2777_, lean_object* v_x_2778_){
_start:
{
if (lean_obj_tag(v_x_2778_) == 0)
{
lean_dec_ref(v_givenNameView_2777_);
lean_dec(v_currNamespace_2776_);
lean_dec(v_auxDeclToFullName_2775_);
lean_dec_ref(v___f_2774_);
lean_dec(v_givenName_2772_);
lean_dec_ref(v_matchLocalDecl_x3f_2771_);
return v_x_2778_;
}
else
{
lean_object* v_val_2779_; uint8_t v___x_2780_; 
v_val_2779_ = lean_ctor_get(v_x_2778_, 0);
v___x_2780_ = l_Lean_LocalDecl_isAuxDecl(v_val_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
lean_inc(v_val_2779_);
lean_dec_ref_known(v_x_2778_, 1);
lean_dec_ref(v_givenNameView_2777_);
lean_dec(v_currNamespace_2776_);
lean_dec(v_auxDeclToFullName_2775_);
lean_dec_ref(v___f_2774_);
v___x_2781_ = lean_apply_2(v_matchLocalDecl_x3f_2771_, v_val_2779_, v_givenName_2772_);
return v___x_2781_;
}
else
{
if (v_skipAuxDecl_2773_ == 0)
{
if (v___x_2780_ == 0)
{
lean_object* v___x_2782_; 
lean_dec_ref_known(v_x_2778_, 1);
lean_dec_ref(v_givenNameView_2777_);
lean_dec(v_currNamespace_2776_);
lean_dec(v_auxDeclToFullName_2775_);
lean_dec_ref(v___f_2774_);
lean_dec(v_givenName_2772_);
lean_dec_ref(v_matchLocalDecl_x3f_2771_);
v___x_2782_ = lean_box(0);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = l_Lean_LocalDecl_fvarId(v_val_2779_);
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2774_, v_auxDeclToFullName_2775_, v___x_2783_);
if (lean_obj_tag(v___x_2784_) == 1)
{
lean_object* v_val_2785_; lean_object* v_fullDeclView_2786_; lean_object* v___y_2788_; lean_object* v_name_2809_; lean_object* v___x_2810_; 
lean_dec(v_givenName_2772_);
lean_dec_ref(v_matchLocalDecl_x3f_2771_);
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v_fullDeclView_2786_ = l_Lean_extractMacroScopes(v_val_2785_);
v_name_2809_ = lean_ctor_get(v_fullDeclView_2786_, 0);
lean_inc(v_name_2809_);
v___x_2810_ = l_Lean_privateToUserName_x3f(v_name_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_inc(v_name_2809_);
v___y_2788_ = v_name_2809_;
goto v___jp_2787_;
}
else
{
lean_object* v_val_2811_; 
v_val_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___y_2788_ = v_val_2811_;
goto v___jp_2787_;
}
v___jp_2787_:
{
lean_object* v_imported_2789_; lean_object* v_ctx_2790_; lean_object* v_scopes_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2807_; 
v_imported_2789_ = lean_ctor_get(v_fullDeclView_2786_, 1);
v_ctx_2790_ = lean_ctor_get(v_fullDeclView_2786_, 2);
v_scopes_2791_ = lean_ctor_get(v_fullDeclView_2786_, 3);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_fullDeclView_2786_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v_fullDeclView_2786_, 0);
lean_dec(v_unused_2808_);
v___x_2793_ = v_fullDeclView_2786_;
v_isShared_2794_ = v_isSharedCheck_2807_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_scopes_2791_);
lean_inc(v_ctx_2790_);
lean_inc(v_imported_2789_);
lean_dec(v_fullDeclView_2786_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2807_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_fullDeclView_2796_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___y_2788_);
v_fullDeclView_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___y_2788_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_imported_2789_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_ctx_2790_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_scopes_2791_);
v_fullDeclView_2796_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v_fullDeclName_2797_; uint8_t v___x_2798_; 
lean_inc_ref(v_fullDeclView_2796_);
v_fullDeclName_2797_ = l_Lean_MacroScopesView_review(v_fullDeclView_2796_);
v___x_2798_ = l_Lean_Name_isPrefixOf(v_currNamespace_2776_, v_fullDeclName_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
lean_inc(v_val_2779_);
lean_dec_ref(v_fullDeclView_2796_);
lean_dec_ref_known(v_x_2778_, 1);
v___x_2799_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2779_, v_givenNameView_2777_, v_fullDeclName_2797_, v_currNamespace_2776_);
lean_dec(v_fullDeclName_2797_);
return v___x_2799_;
}
else
{
lean_object* v___x_2800_; lean_object* v_localDeclNameView_2801_; uint8_t v___x_2802_; 
lean_dec(v_fullDeclName_2797_);
lean_dec(v_currNamespace_2776_);
v___x_2800_ = l_Lean_LocalDecl_userName(v_val_2779_);
v_localDeclNameView_2801_ = l_Lean_extractMacroScopes(v___x_2800_);
v___x_2802_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2801_, v_givenNameView_2777_);
lean_dec_ref(v_localDeclNameView_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
lean_dec_ref(v_fullDeclView_2796_);
lean_dec_ref_known(v_x_2778_, 1);
lean_dec_ref(v_givenNameView_2777_);
v___x_2803_ = lean_box(0);
return v___x_2803_;
}
else
{
uint8_t v___x_2804_; 
v___x_2804_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2777_, v_fullDeclView_2796_);
lean_dec_ref(v_fullDeclView_2796_);
lean_dec_ref(v_givenNameView_2777_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_dec_ref_known(v_x_2778_, 1);
v___x_2805_ = lean_box(0);
return v___x_2805_;
}
else
{
return v_x_2778_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2812_; 
lean_inc(v_val_2779_);
lean_dec(v___x_2784_);
lean_dec_ref_known(v_x_2778_, 1);
lean_dec_ref(v_givenNameView_2777_);
lean_dec(v_currNamespace_2776_);
v___x_2812_ = lean_apply_2(v_matchLocalDecl_x3f_2771_, v_val_2779_, v_givenName_2772_);
return v___x_2812_;
}
}
}
else
{
lean_object* v___x_2813_; 
lean_dec_ref_known(v_x_2778_, 1);
lean_dec_ref(v_givenNameView_2777_);
lean_dec(v_currNamespace_2776_);
lean_dec(v_auxDeclToFullName_2775_);
lean_dec_ref(v___f_2774_);
lean_dec(v_givenName_2772_);
lean_dec_ref(v_matchLocalDecl_x3f_2771_);
v___x_2813_ = lean_box(0);
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2814_, lean_object* v_givenName_2815_, lean_object* v_skipAuxDecl_2816_, lean_object* v___f_2817_, lean_object* v_auxDeclToFullName_2818_, lean_object* v_currNamespace_2819_, lean_object* v_givenNameView_2820_, lean_object* v_x_2821_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2822_; lean_object* v_res_2823_; 
v_skipAuxDecl_boxed_2822_ = lean_unbox(v_skipAuxDecl_2816_);
v_res_2823_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2814_, v_givenName_2815_, v_skipAuxDecl_boxed_2822_, v___f_2817_, v_auxDeclToFullName_2818_, v_currNamespace_2819_, v_givenNameView_2820_, v_x_2821_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2824_, lean_object* v_matchLocalDecl_x3f_2825_, lean_object* v_givenName_2826_, lean_object* v_x_2827_){
_start:
{
if (lean_obj_tag(v_x_2827_) == 0)
{
lean_dec(v_givenName_2826_);
lean_dec_ref(v_matchLocalDecl_x3f_2825_);
return v_x_2827_;
}
else
{
lean_object* v_val_2828_; uint8_t v___x_2829_; 
v_val_2828_ = lean_ctor_get(v_x_2827_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_x_2827_, 1);
v___x_2829_ = l_Lean_LocalDecl_isAuxDecl(v_val_2828_);
if (v___x_2829_ == 0)
{
lean_dec(v_val_2828_);
lean_dec(v_givenName_2826_);
lean_dec_ref(v_matchLocalDecl_x3f_2825_);
lean_inc(v_localDecl_x3f_2824_);
return v_localDecl_x3f_2824_;
}
else
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_apply_2(v_matchLocalDecl_x3f_2825_, v_val_2828_, v_givenName_2826_);
return v___x_2830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2831_, lean_object* v_matchLocalDecl_x3f_2832_, lean_object* v_givenName_2833_, lean_object* v_x_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2831_, v_matchLocalDecl_x3f_2832_, v_givenName_2833_, v_x_2834_);
lean_dec(v_localDecl_x3f_2831_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2855_, lean_object* v_matchLocalDecl_x3f_2856_, lean_object* v___f_2857_, lean_object* v_auxDeclToFullName_2858_, lean_object* v_currNamespace_2859_, lean_object* v_givenNameView_2860_, uint8_t v_skipAuxDecl_2861_){
_start:
{
lean_object* v_decls_2862_; lean_object* v_givenName_2863_; lean_object* v___x_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v_localDecl_x3f_2867_; 
v_decls_2862_ = lean_ctor_get(v_lctx_2855_, 1);
lean_inc_ref_n(v_decls_2862_, 2);
lean_dec_ref(v_lctx_2855_);
lean_inc_ref(v_givenNameView_2860_);
v_givenName_2863_ = l_Lean_MacroScopesView_review(v_givenNameView_2860_);
v___x_2864_ = lean_box(v_skipAuxDecl_2861_);
lean_inc(v_givenName_2863_);
lean_inc_ref(v_matchLocalDecl_x3f_2856_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2865_, 0, v_matchLocalDecl_x3f_2856_);
lean_closure_set(v___f_2865_, 1, v_givenName_2863_);
lean_closure_set(v___f_2865_, 2, v___x_2864_);
lean_closure_set(v___f_2865_, 3, v___f_2857_);
lean_closure_set(v___f_2865_, 4, v_auxDeclToFullName_2858_);
lean_closure_set(v___f_2865_, 5, v_currNamespace_2859_);
lean_closure_set(v___f_2865_, 6, v_givenNameView_2860_);
v___x_2866_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2867_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2866_, v_decls_2862_, v___f_2865_);
if (lean_obj_tag(v_localDecl_x3f_2867_) == 0)
{
if (v_skipAuxDecl_2861_ == 0)
{
lean_object* v___f_2868_; lean_object* v___x_2869_; 
v___f_2868_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2868_, 0, v_localDecl_x3f_2867_);
lean_closure_set(v___f_2868_, 1, v_matchLocalDecl_x3f_2856_);
lean_closure_set(v___f_2868_, 2, v_givenName_2863_);
v___x_2869_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2866_, v_decls_2862_, v___f_2868_);
return v___x_2869_;
}
else
{
lean_dec(v_givenName_2863_);
lean_dec_ref(v_decls_2862_);
lean_dec_ref(v_matchLocalDecl_x3f_2856_);
return v_localDecl_x3f_2867_;
}
}
else
{
lean_dec(v_givenName_2863_);
lean_dec_ref(v_decls_2862_);
lean_dec_ref(v_matchLocalDecl_x3f_2856_);
return v_localDecl_x3f_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2870_, lean_object* v_matchLocalDecl_x3f_2871_, lean_object* v___f_2872_, lean_object* v_auxDeclToFullName_2873_, lean_object* v_currNamespace_2874_, lean_object* v_givenNameView_2875_, lean_object* v_skipAuxDecl_2876_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2877_; lean_object* v_res_2878_; 
v_skipAuxDecl_boxed_2877_ = lean_unbox(v_skipAuxDecl_2876_);
v_res_2878_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2870_, v_matchLocalDecl_x3f_2871_, v___f_2872_, v_auxDeclToFullName_2873_, v_currNamespace_2874_, v_givenNameView_2875_, v_skipAuxDecl_boxed_2877_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2879_, lean_object* v_lctx_2880_, lean_object* v_matchLocalDecl_x3f_2881_, lean_object* v___f_2882_, lean_object* v_auxDeclToFullName_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_currNamespace_2890_){
_start:
{
lean_object* v_view_2891_; lean_object* v_name_2892_; lean_object* v_findLocalDecl_x3f_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; 
v_view_2891_ = l_Lean_extractMacroScopes(v_n_2879_);
v_name_2892_ = lean_ctor_get(v_view_2891_, 0);
lean_inc(v_name_2892_);
v_findLocalDecl_x3f_2893_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2893_, 0, v_lctx_2880_);
lean_closure_set(v_findLocalDecl_x3f_2893_, 1, v_matchLocalDecl_x3f_2881_);
lean_closure_set(v_findLocalDecl_x3f_2893_, 2, v___f_2882_);
lean_closure_set(v_findLocalDecl_x3f_2893_, 3, v_auxDeclToFullName_2883_);
lean_closure_set(v_findLocalDecl_x3f_2893_, 4, v_currNamespace_2890_);
v___x_2894_ = lean_box(0);
v___x_2895_ = 0;
v___x_2896_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2884_, v_inst_2885_, v_inst_2886_, v_inst_2887_, v_inst_2888_, v_inst_2889_, v_view_2891_, v_findLocalDecl_x3f_2893_, v_name_2892_, v___x_2894_, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2897_, lean_object* v_n_2898_, lean_object* v_lctx_2899_, lean_object* v_matchLocalDecl_x3f_2900_, lean_object* v___f_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_toBind_2907_, lean_object* v_____do__lift_2908_){
_start:
{
lean_object* v_auxDeclToFullName_2909_; lean_object* v_getCurrNamespace_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; 
v_auxDeclToFullName_2909_ = lean_ctor_get(v_____do__lift_2908_, 2);
lean_inc(v_auxDeclToFullName_2909_);
lean_dec_ref(v_____do__lift_2908_);
v_getCurrNamespace_2910_ = lean_ctor_get(v_inst_2897_, 0);
lean_inc(v_getCurrNamespace_2910_);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2911_, 0, v_n_2898_);
lean_closure_set(v___f_2911_, 1, v_lctx_2899_);
lean_closure_set(v___f_2911_, 2, v_matchLocalDecl_x3f_2900_);
lean_closure_set(v___f_2911_, 3, v___f_2901_);
lean_closure_set(v___f_2911_, 4, v_auxDeclToFullName_2909_);
lean_closure_set(v___f_2911_, 5, v_inst_2902_);
lean_closure_set(v___f_2911_, 6, v_inst_2897_);
lean_closure_set(v___f_2911_, 7, v_inst_2903_);
lean_closure_set(v___f_2911_, 8, v_inst_2904_);
lean_closure_set(v___f_2911_, 9, v_inst_2905_);
lean_closure_set(v___f_2911_, 10, v_inst_2906_);
v___x_2912_ = lean_apply_4(v_toBind_2907_, lean_box(0), lean_box(0), v_getCurrNamespace_2910_, v___f_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2913_, lean_object* v_n_2914_, lean_object* v_matchLocalDecl_x3f_2915_, lean_object* v___f_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_toBind_2922_, lean_object* v_inst_2923_, lean_object* v_lctx_2924_){
_start:
{
lean_object* v___f_2925_; lean_object* v___x_2926_; 
lean_inc(v_toBind_2922_);
v___f_2925_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2925_, 0, v_inst_2913_);
lean_closure_set(v___f_2925_, 1, v_n_2914_);
lean_closure_set(v___f_2925_, 2, v_lctx_2924_);
lean_closure_set(v___f_2925_, 3, v_matchLocalDecl_x3f_2915_);
lean_closure_set(v___f_2925_, 4, v___f_2916_);
lean_closure_set(v___f_2925_, 5, v_inst_2917_);
lean_closure_set(v___f_2925_, 6, v_inst_2918_);
lean_closure_set(v___f_2925_, 7, v_inst_2919_);
lean_closure_set(v___f_2925_, 8, v_inst_2920_);
lean_closure_set(v___f_2925_, 9, v_inst_2921_);
lean_closure_set(v___f_2925_, 10, v_toBind_2922_);
v___x_2926_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v_inst_2923_, v___f_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_inst_2931_, lean_object* v_inst_2932_, lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_n_2936_){
_start:
{
lean_object* v_toBind_2937_; lean_object* v___f_2938_; lean_object* v_matchLocalDecl_x3f_2939_; lean_object* v___f_2940_; lean_object* v___x_2941_; 
v_toBind_2937_ = lean_ctor_get(v_inst_2929_, 1);
lean_inc_n(v_toBind_2937_, 2);
v___f_2938_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2939_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2935_);
v___f_2940_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2940_, 0, v_inst_2930_);
lean_closure_set(v___f_2940_, 1, v_n_2936_);
lean_closure_set(v___f_2940_, 2, v_matchLocalDecl_x3f_2939_);
lean_closure_set(v___f_2940_, 3, v___f_2938_);
lean_closure_set(v___f_2940_, 4, v_inst_2929_);
lean_closure_set(v___f_2940_, 5, v_inst_2931_);
lean_closure_set(v___f_2940_, 6, v_inst_2932_);
lean_closure_set(v___f_2940_, 7, v_inst_2933_);
lean_closure_set(v___f_2940_, 8, v_inst_2934_);
lean_closure_set(v___f_2940_, 9, v_toBind_2937_);
lean_closure_set(v___f_2940_, 10, v_inst_2935_);
v___x_2941_ = lean_apply_4(v_toBind_2937_, lean_box(0), lean_box(0), v_inst_2935_, v___f_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_n_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_resolveLocalName___redArg(v_inst_2943_, v_inst_2944_, v_inst_2945_, v_inst_2946_, v_inst_2947_, v_inst_2948_, v_inst_2949_, v_n_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2952_, uint8_t v_____do__lift_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_box(v_____do__lift_2953_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
v___x_2956_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2957_, lean_object* v_____do__lift_2958_){
_start:
{
uint8_t v_____do__lift_1060__boxed_2959_; lean_object* v_res_2960_; 
v_____do__lift_1060__boxed_2959_ = lean_unbox(v_____do__lift_2958_);
v_res_2960_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2957_, v_____do__lift_1060__boxed_2959_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2961_, lean_object* v___y_2962_, lean_object* v_____do__lift_2963_){
_start:
{
if (lean_obj_tag(v_____do__lift_2963_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v___y_2962_);
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_apply_2(v_toPure_2961_, lean_box(0), v___x_2964_);
return v___x_2965_;
}
else
{
lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2973_; 
v_isSharedCheck_2973_ = !lean_is_exclusive(v_____do__lift_2963_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v_____do__lift_2963_, 0);
lean_dec(v_unused_2974_);
v___x_2967_ = v_____do__lift_2963_;
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
else
{
lean_dec(v_____do__lift_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___y_2962_);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___y_2962_);
v___x_2970_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_apply_2(v_toPure_2961_, lean_box(0), v___x_2970_);
return v___x_2971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2977_, lean_object* v_toBind_2978_, lean_object* v___f_2979_, lean_object* v_____do__lift_2980_){
_start:
{
if (lean_obj_tag(v_____do__lift_2980_) == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec(v___f_2979_);
lean_dec(v_toBind_2978_);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_apply_2(v_toPure_2977_, lean_box(0), v___x_2981_);
return v___x_2982_;
}
else
{
lean_object* v_val_2983_; uint8_t v___x_2984_; 
v_val_2983_ = lean_ctor_get(v_____do__lift_2980_, 0);
v___x_2984_ = lean_unbox(v_val_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_apply_2(v_toPure_2977_, lean_box(0), v___x_2985_);
v___x_2987_ = lean_apply_4(v_toBind_2978_, lean_box(0), lean_box(0), v___x_2986_, v___f_2979_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2989_ = lean_apply_2(v_toPure_2977_, lean_box(0), v___x_2988_);
v___x_2990_ = lean_apply_4(v_toBind_2978_, lean_box(0), lean_box(0), v___x_2989_, v___f_2979_);
return v___x_2990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2991_, lean_object* v_toBind_2992_, lean_object* v___f_2993_, lean_object* v_____do__lift_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2991_, v_toBind_2992_, v___f_2993_, v_____do__lift_2994_);
lean_dec(v_____do__lift_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2996_, lean_object* v_filter_2997_, lean_object* v___y_2998_, lean_object* v_toBind_2999_, lean_object* v___f_3000_, lean_object* v___f_3001_, lean_object* v_____do__lift_3002_){
_start:
{
if (lean_obj_tag(v_____do__lift_3002_) == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v___f_3001_);
lean_dec(v___f_3000_);
lean_dec(v_toBind_2999_);
lean_dec(v___y_2998_);
lean_dec(v_filter_2997_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_apply_2(v_toPure_2996_, lean_box(0), v___x_3003_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec(v_toPure_2996_);
v___x_3005_ = lean_apply_1(v_filter_2997_, v___y_2998_);
lean_inc(v_toBind_2999_);
v___x_3006_ = lean_apply_4(v_toBind_2999_, lean_box(0), lean_box(0), v___x_3005_, v___f_3000_);
v___x_3007_ = lean_apply_4(v_toBind_2999_, lean_box(0), lean_box(0), v___x_3006_, v___f_3001_);
return v___x_3007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3008_, lean_object* v_filter_3009_, lean_object* v___y_3010_, lean_object* v_toBind_3011_, lean_object* v___f_3012_, lean_object* v___f_3013_, lean_object* v_____do__lift_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3008_, v_filter_3009_, v___y_3010_, v_toBind_3011_, v___f_3012_, v___f_3013_, v_____do__lift_3014_);
lean_dec(v_____do__lift_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3016_, lean_object* v_n_u2080_3017_, lean_object* v_toBind_3018_, lean_object* v___f_3019_, lean_object* v_____do__lift_3020_){
_start:
{
if (lean_obj_tag(v_____do__lift_3020_) == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_dec(v___f_3019_);
lean_dec(v_toBind_3018_);
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_apply_2(v_toPure_3016_, lean_box(0), v___x_3024_);
return v___x_3025_;
}
else
{
lean_object* v_val_3026_; 
v_val_3026_ = lean_ctor_get(v_____do__lift_3020_, 0);
if (lean_obj_tag(v_val_3026_) == 1)
{
lean_object* v_tail_3027_; 
v_tail_3027_ = lean_ctor_get(v_val_3026_, 1);
if (lean_obj_tag(v_tail_3027_) == 0)
{
lean_object* v_head_3028_; lean_object* v_fst_3029_; uint8_t v___x_3030_; 
v_head_3028_ = lean_ctor_get(v_val_3026_, 0);
v_fst_3029_ = lean_ctor_get(v_head_3028_, 0);
v___x_3030_ = lean_name_eq(v_fst_3029_, v_n_u2080_3017_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = lean_box(0);
v___x_3032_ = lean_apply_2(v_toPure_3016_, lean_box(0), v___x_3031_);
v___x_3033_ = lean_apply_4(v_toBind_3018_, lean_box(0), lean_box(0), v___x_3032_, v___f_3019_);
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3035_ = lean_apply_2(v_toPure_3016_, lean_box(0), v___x_3034_);
v___x_3036_ = lean_apply_4(v_toBind_3018_, lean_box(0), lean_box(0), v___x_3035_, v___f_3019_);
return v___x_3036_;
}
}
else
{
lean_dec(v___f_3019_);
lean_dec(v_toBind_3018_);
goto v___jp_3021_;
}
}
else
{
lean_dec(v___f_3019_);
lean_dec(v_toBind_3018_);
goto v___jp_3021_;
}
}
v___jp_3021_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = lean_apply_2(v_toPure_3016_, lean_box(0), v___x_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3037_, lean_object* v_n_u2080_3038_, lean_object* v_toBind_3039_, lean_object* v___f_3040_, lean_object* v_____do__lift_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3037_, v_n_u2080_3038_, v_toBind_3039_, v___f_3040_, v_____do__lift_3041_);
lean_dec(v_____do__lift_3041_);
lean_dec(v_n_u2080_3038_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_n_u2080_3049_, lean_object* v_filter_3050_, lean_object* v_view_x3f_3051_, lean_object* v_n_3052_){
_start:
{
lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v_toApplicative_3065_; lean_object* v_getEnv_3066_; lean_object* v_modifyEnv_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3105_; 
lean_inc_ref_n(v_inst_3043_, 8);
v___f_3053_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3053_, 0, v_inst_3043_);
v___f_3054_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3054_, 0, v_inst_3043_);
v___f_3055_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3055_, 0, v_inst_3043_);
v___f_3056_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3056_, 0, v_inst_3043_);
v___f_3057_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3057_, 0, v_inst_3043_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___f_3053_);
lean_ctor_set(v___x_3058_, 1, v___f_3054_);
v___x_3059_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3059_, 0, lean_box(0));
lean_closure_set(v___x_3059_, 1, v_inst_3043_);
v___x_3060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
lean_ctor_set(v___x_3060_, 2, v___f_3055_);
lean_ctor_set(v___x_3060_, 3, v___f_3056_);
lean_ctor_set(v___x_3060_, 4, v___f_3057_);
v___x_3061_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3061_, 0, lean_box(0));
lean_closure_set(v___x_3061_, 1, v_inst_3043_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3063_, 0, lean_box(0));
lean_closure_set(v___x_3063_, 1, v_inst_3043_);
lean_inc_ref(v___x_3063_);
v___x_3064_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3063_, v_inst_3044_);
v_toApplicative_3065_ = lean_ctor_get(v_inst_3043_, 0);
lean_inc_ref(v_toApplicative_3065_);
v_getEnv_3066_ = lean_ctor_get(v_inst_3045_, 0);
v_modifyEnv_3067_ = lean_ctor_get(v_inst_3045_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_inst_3045_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3069_ = v_inst_3045_;
v_isShared_3070_ = v_isSharedCheck_3105_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_modifyEnv_3067_);
lean_inc(v_getEnv_3066_);
lean_dec(v_inst_3045_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3105_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_toBind_3071_; lean_object* v_toPure_3072_; lean_object* v___f_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v_toBind_3071_ = lean_ctor_get(v_inst_3043_, 1);
lean_inc_n(v_toBind_3071_, 2);
lean_dec_ref(v_inst_3043_);
v_toPure_3072_ = lean_ctor_get(v_toApplicative_3065_, 1);
lean_inc_n(v_toPure_3072_, 3);
lean_dec_ref(v_toApplicative_3065_);
lean_inc_ref(v___x_3063_);
v___f_3073_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3073_, 0, v_modifyEnv_3067_);
lean_closure_set(v___f_3073_, 1, v___x_3063_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3074_, 0, v_toPure_3072_);
v___f_3075_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3075_, 0, v_toPure_3072_);
v___x_3076_ = lean_apply_4(v_toBind_3071_, lean_box(0), lean_box(0), v_getEnv_3066_, v___f_3075_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v___f_3073_);
lean_ctor_set(v___x_3069_, 0, v___x_3076_);
v___x_3078_ = v___x_3069_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___f_3073_);
v___x_3078_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; lean_object* v___y_3083_; 
lean_inc_ref_n(v___x_3063_, 2);
v___x_3079_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_3063_, v_inst_3046_);
v___x_3080_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3063_, v_inst_3047_);
v___f_3081_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3081_, 0, v_inst_3048_);
lean_closure_set(v___f_3081_, 1, v___x_3063_);
if (lean_obj_tag(v_view_x3f_3051_) == 1)
{
lean_object* v_val_3091_; lean_object* v_imported_3092_; lean_object* v_ctx_3093_; lean_object* v_scopes_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_val_3091_ = lean_ctor_get(v_view_x3f_3051_, 0);
lean_inc(v_val_3091_);
lean_dec_ref_known(v_view_x3f_3051_, 1);
v_imported_3092_ = lean_ctor_get(v_val_3091_, 1);
v_ctx_3093_ = lean_ctor_get(v_val_3091_, 2);
v_scopes_3094_ = lean_ctor_get(v_val_3091_, 3);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_val_3091_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v_val_3091_, 0);
lean_dec(v_unused_3103_);
v___x_3096_ = v_val_3091_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_scopes_3094_);
lean_inc(v_ctx_3093_);
lean_inc(v_imported_3092_);
lean_dec(v_val_3091_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v_n_3052_);
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_n_3052_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_imported_3092_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_ctx_3093_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_scopes_3094_);
v___x_3099_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_MacroScopesView_review(v___x_3099_);
v___y_3083_ = v___x_3100_;
goto v___jp_3082_;
}
}
}
else
{
lean_dec(v_view_x3f_3051_);
v___y_3083_ = v_n_3052_;
goto v___jp_3082_;
}
v___jp_3082_:
{
lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___f_3086_; lean_object* v___f_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_inc_n(v___y_3083_, 2);
lean_inc_n(v_toPure_3072_, 3);
v___f_3084_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3084_, 0, v_toPure_3072_);
lean_closure_set(v___f_3084_, 1, v___y_3083_);
lean_inc_n(v_toBind_3071_, 3);
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3085_, 0, v_toPure_3072_);
lean_closure_set(v___f_3085_, 1, v_toBind_3071_);
lean_closure_set(v___f_3085_, 2, v___f_3084_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3086_, 0, v_toPure_3072_);
lean_closure_set(v___f_3086_, 1, v_filter_3050_);
lean_closure_set(v___f_3086_, 2, v___y_3083_);
lean_closure_set(v___f_3086_, 3, v_toBind_3071_);
lean_closure_set(v___f_3086_, 4, v___f_3074_);
lean_closure_set(v___f_3086_, 5, v___f_3085_);
v___f_3087_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3087_, 0, v_toPure_3072_);
lean_closure_set(v___f_3087_, 1, v_n_u2080_3049_);
lean_closure_set(v___f_3087_, 2, v_toBind_3071_);
lean_closure_set(v___f_3087_, 3, v___f_3086_);
v___x_3088_ = 0;
v___x_3089_ = l_Lean_resolveGlobalName___redArg(v___x_3062_, v___x_3064_, v___x_3078_, v___x_3079_, v___x_3080_, v___f_3081_, v___y_3083_, v___x_3088_);
v___x_3090_ = lean_apply_4(v_toBind_3071_, lean_box(0), lean_box(0), v___x_3089_, v___f_3087_);
return v___x_3090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3106_, lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_n_u2080_3113_, lean_object* v_filter_3114_, lean_object* v_view_x3f_3115_, lean_object* v_n_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3107_, v_inst_3108_, v_inst_3109_, v_inst_3110_, v_inst_3111_, v_inst_3112_, v_n_u2080_3113_, v_filter_3114_, v_view_x3f_3115_, v_n_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3122_, lean_object* v_____x_3123_){
_start:
{
if (lean_obj_tag(v_____x_3123_) == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3125_ = lean_apply_2(v_toPure_3122_, lean_box(0), v___x_3124_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; 
v___x_3126_ = lean_apply_2(v_toPure_3122_, lean_box(0), v_____x_3123_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3127_, lean_object* v_____do__lift_3128_){
_start:
{
if (lean_obj_tag(v_____do__lift_3128_) == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_apply_2(v_toPure_3127_, lean_box(0), v___x_3129_);
return v___x_3130_;
}
else
{
lean_object* v_val_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3140_; 
v_val_3131_ = lean_ctor_get(v_____do__lift_3128_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_____do__lift_3128_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3133_ = v_____do__lift_3128_;
v_isShared_3134_ = v_isSharedCheck_3140_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_val_3131_);
lean_dec(v_____do__lift_3128_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3140_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_val_3131_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_apply_2(v_toPure_3127_, lean_box(0), v___x_3137_);
return v___x_3138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3141_, lean_object* v___x_3142_, lean_object* v_____do__lift_3143_){
_start:
{
if (lean_obj_tag(v_____do__lift_3143_) == 0)
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_apply_2(v_toPure_3141_, lean_box(0), v___x_3142_);
return v___x_3144_;
}
else
{
lean_object* v_val_3145_; lean_object* v_fst_3146_; lean_object* v___x_3147_; 
lean_dec(v___x_3142_);
v_val_3145_ = lean_ctor_get(v_____do__lift_3143_, 0);
lean_inc(v_val_3145_);
lean_dec_ref_known(v_____do__lift_3143_, 1);
v_fst_3146_ = lean_ctor_get(v_val_3145_, 0);
lean_inc(v_fst_3146_);
lean_dec(v_val_3145_);
v___x_3147_ = lean_apply_2(v_toPure_3141_, lean_box(0), v_fst_3146_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3148_, lean_object* v___x_3149_, lean_object* v___x_3150_, lean_object* v_____do__lift_3151_){
_start:
{
if (lean_obj_tag(v_____do__lift_3151_) == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec(v___x_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3152_);
return v___x_3153_;
}
else
{
lean_object* v_val_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3185_; 
v_val_3154_ = lean_ctor_get(v_____do__lift_3151_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_____do__lift_3151_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3156_ = v_____do__lift_3151_;
v_isShared_3157_ = v_isSharedCheck_3185_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_val_3154_);
lean_dec(v_____do__lift_3151_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3185_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
if (lean_obj_tag(v_val_3154_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v___x_3150_);
v_a_3158_ = lean_ctor_get(v_val_3154_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_val_3154_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3160_ = v_val_3154_;
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v_val_3154_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v_a_3158_);
v___x_3163_ = v___x_3156_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3149_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3164_);
v___x_3166_ = v___x_3160_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
v___x_3168_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3167_);
return v___x_3168_;
}
}
}
}
else
{
lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3183_; 
v_isSharedCheck_3183_ = !lean_is_exclusive(v_val_3154_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; 
v_unused_3184_ = lean_ctor_get(v_val_3154_, 0);
lean_dec(v_unused_3184_);
v___x_3173_ = v_val_3154_;
v_isShared_3174_ = v_isSharedCheck_3183_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v_val_3154_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3183_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3150_);
lean_ctor_set(v___x_3175_, 1, v___x_3149_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v___x_3175_);
v___x_3177_ = v___x_3173_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3179_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v___x_3177_);
v___x_3179_ = v___x_3156_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3179_);
return v___x_3180_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3186_, lean_object* v___x_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_n_u2080_3194_, lean_object* v_filter_3195_, lean_object* v_view_x3f_3196_, lean_object* v_toBind_3197_, lean_object* v___f_3198_, lean_object* v___f_3199_, lean_object* v_a_3200_, lean_object* v_x_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_snd_3203_; lean_object* v___x_3204_; lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_snd_3203_ = lean_ctor_get(v___y_3202_, 1);
lean_inc(v_snd_3203_);
lean_dec_ref(v___y_3202_);
v___x_3204_ = l_Lean_Name_appendCore(v_a_3200_, v_snd_3203_);
lean_inc(v___x_3204_);
v___f_3205_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3205_, 0, v_toPure_3186_);
lean_closure_set(v___f_3205_, 1, v___x_3204_);
lean_closure_set(v___f_3205_, 2, v___x_3187_);
v___x_3206_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3188_, v_inst_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_inst_3193_, v_n_u2080_3194_, v_filter_3195_, v_view_x3f_3196_, v___x_3204_);
lean_inc_n(v_toBind_3197_, 2);
v___x_3207_ = lean_apply_4(v_toBind_3197_, lean_box(0), lean_box(0), v___x_3206_, v___f_3198_);
v___x_3208_ = lean_apply_4(v_toBind_3197_, lean_box(0), lean_box(0), v___x_3207_, v___f_3199_);
v___x_3209_ = lean_apply_4(v_toBind_3197_, lean_box(0), lean_box(0), v___x_3208_, v___f_3205_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3210_ = _args[0];
lean_object* v___x_3211_ = _args[1];
lean_object* v_inst_3212_ = _args[2];
lean_object* v_inst_3213_ = _args[3];
lean_object* v_inst_3214_ = _args[4];
lean_object* v_inst_3215_ = _args[5];
lean_object* v_inst_3216_ = _args[6];
lean_object* v_inst_3217_ = _args[7];
lean_object* v_n_u2080_3218_ = _args[8];
lean_object* v_filter_3219_ = _args[9];
lean_object* v_view_x3f_3220_ = _args[10];
lean_object* v_toBind_3221_ = _args[11];
lean_object* v___f_3222_ = _args[12];
lean_object* v___f_3223_ = _args[13];
lean_object* v_a_3224_ = _args[14];
lean_object* v_x_3225_ = _args[15];
lean_object* v___y_3226_ = _args[16];
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3210_, v___x_3211_, v_inst_3212_, v_inst_3213_, v_inst_3214_, v_inst_3215_, v_inst_3216_, v_inst_3217_, v_n_u2080_3218_, v_filter_3219_, v_view_x3f_3220_, v_toBind_3221_, v___f_3222_, v___f_3223_, v_a_3224_, v_x_3225_, v___y_3226_);
lean_dec(v_a_3224_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3231_, lean_object* v_n_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_n_u2080_3239_, lean_object* v_filter_3240_, lean_object* v_view_x3f_3241_, lean_object* v_toBind_3242_, lean_object* v___f_3243_, lean_object* v___f_3244_, lean_object* v___x_3245_, lean_object* v_____do__lift_3246_){
_start:
{
if (lean_obj_tag(v_____do__lift_3246_) == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_dec_ref(v___x_3245_);
lean_dec(v___f_3244_);
lean_dec(v___f_3243_);
lean_dec(v_toBind_3242_);
lean_dec(v_view_x3f_3241_);
lean_dec(v_filter_3240_);
lean_dec(v_n_u2080_3239_);
lean_dec(v_inst_3238_);
lean_dec_ref(v_inst_3237_);
lean_dec_ref(v_inst_3236_);
lean_dec_ref(v_inst_3235_);
lean_dec_ref(v_inst_3234_);
lean_dec_ref(v_inst_3233_);
lean_dec(v_n_3232_);
v___x_3247_ = lean_box(0);
v___x_3248_ = lean_apply_2(v_toPure_3231_, lean_box(0), v___x_3247_);
return v___x_3248_;
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___f_3252_; lean_object* v___f_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3249_ = l_Lean_privateToUserName(v_n_3232_);
v___x_3250_ = l_Lean_Name_componentsRev(v___x_3249_);
v___x_3251_ = lean_box(0);
lean_inc(v_toPure_3231_);
v___f_3252_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3252_, 0, v_toPure_3231_);
lean_closure_set(v___f_3252_, 1, v___x_3251_);
lean_inc(v_toBind_3242_);
v___f_3253_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3253_, 0, v_toPure_3231_);
lean_closure_set(v___f_3253_, 1, v___x_3251_);
lean_closure_set(v___f_3253_, 2, v_inst_3233_);
lean_closure_set(v___f_3253_, 3, v_inst_3234_);
lean_closure_set(v___f_3253_, 4, v_inst_3235_);
lean_closure_set(v___f_3253_, 5, v_inst_3236_);
lean_closure_set(v___f_3253_, 6, v_inst_3237_);
lean_closure_set(v___f_3253_, 7, v_inst_3238_);
lean_closure_set(v___f_3253_, 8, v_n_u2080_3239_);
lean_closure_set(v___f_3253_, 9, v_filter_3240_);
lean_closure_set(v___f_3253_, 10, v_view_x3f_3241_);
lean_closure_set(v___f_3253_, 11, v_toBind_3242_);
lean_closure_set(v___f_3253_, 12, v___f_3243_);
lean_closure_set(v___f_3253_, 13, v___f_3244_);
v___x_3254_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3255_ = l_List_forIn_x27_loop___redArg(v___x_3245_, v___f_3253_, v___x_3250_, v___x_3254_);
lean_dec(v___x_3250_);
v___x_3256_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3255_, v___f_3252_);
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3257_, lean_object* v_n_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_inst_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_n_u2080_3265_, lean_object* v_filter_3266_, lean_object* v_view_x3f_3267_, lean_object* v_toBind_3268_, lean_object* v___f_3269_, lean_object* v___f_3270_, lean_object* v___x_3271_, lean_object* v_____do__lift_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3257_, v_n_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_inst_3262_, v_inst_3263_, v_inst_3264_, v_n_u2080_3265_, v_filter_3266_, v_view_x3f_3267_, v_toBind_3268_, v___f_3269_, v___f_3270_, v___x_3271_, v_____do__lift_3272_);
lean_dec(v_____do__lift_3272_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_n_u2080_3280_, lean_object* v_filter_3281_, lean_object* v_view_x3f_3282_, lean_object* v_n_3283_){
_start:
{
lean_object* v___f_3284_; lean_object* v___f_3285_; lean_object* v___f_3286_; lean_object* v___f_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___y_3295_; uint8_t v___x_3303_; 
lean_inc_ref_n(v_inst_3274_, 7);
v___f_3284_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3284_, 0, v_inst_3274_);
v___f_3285_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3285_, 0, v_inst_3274_);
v___f_3286_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3286_, 0, v_inst_3274_);
v___f_3287_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3287_, 0, v_inst_3274_);
v___f_3288_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3288_, 0, v_inst_3274_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___f_3284_);
lean_ctor_set(v___x_3289_, 1, v___f_3285_);
v___x_3290_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3290_, 0, lean_box(0));
lean_closure_set(v___x_3290_, 1, v_inst_3274_);
v___x_3291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
lean_ctor_set(v___x_3291_, 2, v___f_3286_);
lean_ctor_set(v___x_3291_, 3, v___f_3287_);
lean_ctor_set(v___x_3291_, 4, v___f_3288_);
v___x_3292_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3292_, 0, lean_box(0));
lean_closure_set(v___x_3292_, 1, v_inst_3274_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3303_ = l_Lean_Name_hasMacroScopes(v_n_3283_);
if (v___x_3303_ == 0)
{
lean_object* v_toApplicative_3304_; lean_object* v_toPure_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_toApplicative_3304_ = lean_ctor_get(v_inst_3274_, 0);
v_toPure_3305_ = lean_ctor_get(v_toApplicative_3304_, 1);
v___x_3306_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3305_);
v___x_3307_ = lean_apply_2(v_toPure_3305_, lean_box(0), v___x_3306_);
v___y_3295_ = v___x_3307_;
goto v___jp_3294_;
}
else
{
lean_object* v_toApplicative_3308_; lean_object* v_toPure_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_toApplicative_3308_ = lean_ctor_get(v_inst_3274_, 0);
v_toPure_3309_ = lean_ctor_get(v_toApplicative_3308_, 1);
v___x_3310_ = lean_box(0);
lean_inc(v_toPure_3309_);
v___x_3311_ = lean_apply_2(v_toPure_3309_, lean_box(0), v___x_3310_);
v___y_3295_ = v___x_3311_;
goto v___jp_3294_;
}
v___jp_3294_:
{
lean_object* v_toApplicative_3296_; lean_object* v_toBind_3297_; lean_object* v_toPure_3298_; lean_object* v___f_3299_; lean_object* v___f_3300_; lean_object* v___f_3301_; lean_object* v___x_3302_; 
v_toApplicative_3296_ = lean_ctor_get(v_inst_3274_, 0);
v_toBind_3297_ = lean_ctor_get(v_inst_3274_, 1);
lean_inc_n(v_toBind_3297_, 2);
v_toPure_3298_ = lean_ctor_get(v_toApplicative_3296_, 1);
lean_inc_n(v_toPure_3298_, 3);
v___f_3299_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3299_, 0, v_toPure_3298_);
v___f_3300_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3300_, 0, v_toPure_3298_);
v___f_3301_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3301_, 0, v_toPure_3298_);
lean_closure_set(v___f_3301_, 1, v_n_3283_);
lean_closure_set(v___f_3301_, 2, v_inst_3274_);
lean_closure_set(v___f_3301_, 3, v_inst_3275_);
lean_closure_set(v___f_3301_, 4, v_inst_3276_);
lean_closure_set(v___f_3301_, 5, v_inst_3277_);
lean_closure_set(v___f_3301_, 6, v_inst_3278_);
lean_closure_set(v___f_3301_, 7, v_inst_3279_);
lean_closure_set(v___f_3301_, 8, v_n_u2080_3280_);
lean_closure_set(v___f_3301_, 9, v_filter_3281_);
lean_closure_set(v___f_3301_, 10, v_view_x3f_3282_);
lean_closure_set(v___f_3301_, 11, v_toBind_3297_);
lean_closure_set(v___f_3301_, 12, v___f_3300_);
lean_closure_set(v___f_3301_, 13, v___f_3299_);
lean_closure_set(v___f_3301_, 14, v___x_3293_);
v___x_3302_ = lean_apply_4(v_toBind_3297_, lean_box(0), lean_box(0), v___y_3295_, v___f_3301_);
return v___x_3302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_n_u2080_3319_, lean_object* v_filter_3320_, lean_object* v_view_x3f_3321_, lean_object* v_n_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3313_, v_inst_3314_, v_inst_3315_, v_inst_3316_, v_inst_3317_, v_inst_3318_, v_n_u2080_3319_, v_filter_3320_, v_view_x3f_3321_, v_n_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3324_, lean_object* v_x1_3325_, lean_object* v_x2_3326_){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3327_ = l_Lean_Name_getPrefix(v_x2_3326_);
v___x_3328_ = l_Lean_Name_getPrefix(v_n_u2081_3324_);
v___x_3329_ = l_Lean_Name_isPrefixOf(v___x_3327_, v___x_3328_);
lean_dec(v___x_3328_);
lean_dec(v___x_3327_);
if (v___x_3329_ == 0)
{
lean_dec(v_x2_3326_);
return v_x1_3325_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_array_push(v_x1_3325_, v_x2_3326_);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3331_, lean_object* v_x1_3332_, lean_object* v_x2_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3331_, v_x1_3332_, v_x2_3333_);
lean_dec(v_n_u2081_3331_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3335_, lean_object* v_n_u2081_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_n_u2080_3343_, lean_object* v_filter_3344_, lean_object* v_toPure_3345_, lean_object* v_____do__lift_3346_){
_start:
{
if (lean_obj_tag(v_____do__lift_3346_) == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec(v_toPure_3345_);
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_view_3335_);
v___x_3348_ = l_Lean_rootNamespace;
v___x_3349_ = l_Lean_Name_append(v___x_3348_, v_n_u2081_3336_);
v___x_3350_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3337_, v_inst_3338_, v_inst_3339_, v_inst_3340_, v_inst_3341_, v_inst_3342_, v_n_u2080_3343_, v_filter_3344_, v___x_3347_, v___x_3349_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; 
lean_dec(v_filter_3344_);
lean_dec(v_n_u2080_3343_);
lean_dec(v_inst_3342_);
lean_dec_ref(v_inst_3341_);
lean_dec_ref(v_inst_3340_);
lean_dec_ref(v_inst_3339_);
lean_dec_ref(v_inst_3338_);
lean_dec_ref(v_inst_3337_);
lean_dec(v_n_u2081_3336_);
lean_dec_ref(v_view_3335_);
v___x_3351_ = lean_apply_2(v_toPure_3345_, lean_box(0), v_____do__lift_3346_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3352_, lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_n_u2080_3359_, lean_object* v_filter_3360_, lean_object* v___x_3361_, lean_object* v_toBind_3362_, lean_object* v___f_3363_, uint8_t v_allowHorizAliases_3364_, lean_object* v___f_3365_, lean_object* v_____do__lift_3366_){
_start:
{
lean_object* v_aliases_3368_; 
if (lean_obj_tag(v_____do__lift_3366_) == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___f_3365_);
lean_dec(v___f_3363_);
lean_dec(v_toBind_3362_);
lean_dec_ref(v___x_3361_);
lean_dec(v_filter_3360_);
lean_dec(v_n_u2080_3359_);
lean_dec(v_inst_3358_);
lean_dec_ref(v_inst_3357_);
lean_dec_ref(v_inst_3356_);
lean_dec_ref(v_inst_3355_);
lean_dec_ref(v_inst_3354_);
lean_dec_ref(v_inst_3353_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_apply_2(v_toPure_3352_, lean_box(0), v___x_3374_);
return v___x_3375_;
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v_toPure_3352_);
v_val_3376_ = lean_ctor_get(v_____do__lift_3366_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_____do__lift_3366_, 1);
lean_inc(v_n_u2080_3359_);
v___x_3377_ = l_Lean_getRevAliases(v_val_3376_, v_n_u2080_3359_);
v___x_3378_ = lean_array_mk(v___x_3377_);
if (v_allowHorizAliases_3364_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = lean_array_get_size(v___x_3378_);
v___x_3381_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3382_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3383_ = lean_nat_dec_lt(v___x_3379_, v___x_3380_);
if (v___x_3383_ == 0)
{
lean_dec_ref(v___x_3378_);
lean_dec_ref(v___f_3365_);
v_aliases_3368_ = v___x_3381_;
goto v___jp_3367_;
}
else
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_nat_dec_le(v___x_3380_, v___x_3380_);
if (v___x_3384_ == 0)
{
if (v___x_3383_ == 0)
{
lean_dec_ref(v___x_3378_);
lean_dec_ref(v___f_3365_);
v_aliases_3368_ = v___x_3381_;
goto v___jp_3367_;
}
else
{
size_t v___x_3385_; size_t v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = lean_usize_of_nat(v___x_3380_);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3382_, v___f_3365_, v___x_3378_, v___x_3385_, v___x_3386_, v___x_3381_);
v_aliases_3368_ = v___x_3387_;
goto v___jp_3367_;
}
}
else
{
size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = lean_usize_of_nat(v___x_3380_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3382_, v___f_3365_, v___x_3378_, v___x_3388_, v___x_3389_, v___x_3381_);
v_aliases_3368_ = v___x_3390_;
goto v___jp_3367_;
}
}
}
else
{
lean_dec_ref(v___f_3365_);
v_aliases_3368_ = v___x_3378_;
goto v___jp_3367_;
}
}
v___jp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3370_, 0, lean_box(0));
lean_closure_set(v___x_3370_, 1, v_inst_3353_);
lean_closure_set(v___x_3370_, 2, v_inst_3354_);
lean_closure_set(v___x_3370_, 3, v_inst_3355_);
lean_closure_set(v___x_3370_, 4, v_inst_3356_);
lean_closure_set(v___x_3370_, 5, v_inst_3357_);
lean_closure_set(v___x_3370_, 6, v_inst_3358_);
lean_closure_set(v___x_3370_, 7, v_n_u2080_3359_);
lean_closure_set(v___x_3370_, 8, v_filter_3360_);
lean_closure_set(v___x_3370_, 9, v___x_3369_);
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3361_, v___x_3370_, v_aliases_3368_, v___x_3371_);
v___x_3373_ = lean_apply_4(v_toBind_3362_, lean_box(0), lean_box(0), v___x_3372_, v___f_3363_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_inst_3396_, lean_object* v_inst_3397_, lean_object* v_n_u2080_3398_, lean_object* v_filter_3399_, lean_object* v___x_3400_, lean_object* v_toBind_3401_, lean_object* v___f_3402_, lean_object* v_allowHorizAliases_3403_, lean_object* v___f_3404_, lean_object* v_____do__lift_3405_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3406_; lean_object* v_res_3407_; 
v_allowHorizAliases_boxed_3406_ = lean_unbox(v_allowHorizAliases_3403_);
v_res_3407_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3391_, v_inst_3392_, v_inst_3393_, v_inst_3394_, v_inst_3395_, v_inst_3396_, v_inst_3397_, v_n_u2080_3398_, v_filter_3399_, v___x_3400_, v_toBind_3401_, v___f_3402_, v_allowHorizAliases_boxed_3406_, v___f_3404_, v_____do__lift_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3408_, lean_object* v_____do__lift_3409_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v_____do__lift_3409_);
v___x_3411_ = lean_apply_2(v_toPure_3408_, lean_box(0), v___x_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3412_, lean_object* v_inst_3413_, lean_object* v_inst_3414_, lean_object* v_inst_3415_, lean_object* v_inst_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_n_u2080_3419_, lean_object* v_filter_3420_, lean_object* v___x_3421_, lean_object* v_toPure_3422_, lean_object* v_____do__lift_3423_){
_start:
{
if (lean_obj_tag(v_____do__lift_3423_) == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
lean_dec(v_toPure_3422_);
v___x_3424_ = l_Lean_rootNamespace;
v___x_3425_ = l_Lean_Name_append(v___x_3424_, v_n_u2081_3412_);
v___x_3426_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3413_, v_inst_3414_, v_inst_3415_, v_inst_3416_, v_inst_3417_, v_inst_3418_, v_n_u2080_3419_, v_filter_3420_, v___x_3421_, v___x_3425_);
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; 
lean_dec(v___x_3421_);
lean_dec(v_filter_3420_);
lean_dec(v_n_u2080_3419_);
lean_dec(v_inst_3418_);
lean_dec_ref(v_inst_3417_);
lean_dec_ref(v_inst_3416_);
lean_dec_ref(v_inst_3415_);
lean_dec_ref(v_inst_3414_);
lean_dec_ref(v_inst_3413_);
lean_dec(v_n_u2081_3412_);
v___x_3427_ = lean_apply_2(v_toPure_3422_, lean_box(0), v_____do__lift_3423_);
return v___x_3427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3428_, lean_object* v_inst_3429_, lean_object* v_inst_3430_, lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_n_u2080_3434_, uint8_t v_fullNames_3435_, uint8_t v_allowHorizAliases_3436_, lean_object* v_filter_3437_){
_start:
{
lean_object* v_view_3438_; lean_object* v_name_3439_; lean_object* v_n_u2081_3440_; lean_object* v___x_3441_; 
lean_inc(v_n_u2080_3434_);
v_view_3438_ = l_Lean_extractMacroScopes(v_n_u2080_3434_);
v_name_3439_ = lean_ctor_get(v_view_3438_, 0);
lean_inc(v_name_3439_);
v_n_u2081_3440_ = l_Lean_privateToUserName(v_name_3439_);
lean_inc_ref(v_inst_3428_);
v___x_3441_ = l_OptionT_instAlternative___redArg(v_inst_3428_);
if (v_fullNames_3435_ == 0)
{
lean_object* v_toApplicative_3442_; lean_object* v_getEnv_3443_; lean_object* v_toBind_3444_; lean_object* v_toPure_3445_; lean_object* v___f_3446_; lean_object* v___f_3447_; lean_object* v___x_3448_; lean_object* v___f_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_toApplicative_3442_ = lean_ctor_get(v_inst_3428_, 0);
v_getEnv_3443_ = lean_ctor_get(v_inst_3430_, 0);
lean_inc(v_getEnv_3443_);
v_toBind_3444_ = lean_ctor_get(v_inst_3428_, 1);
lean_inc_n(v_toBind_3444_, 3);
v_toPure_3445_ = lean_ctor_get(v_toApplicative_3442_, 1);
lean_inc_n(v_toPure_3445_, 3);
lean_inc(v_n_u2081_3440_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3446_, 0, v_n_u2081_3440_);
lean_inc(v_filter_3437_);
lean_inc(v_n_u2080_3434_);
lean_inc(v_inst_3433_);
lean_inc_ref(v_inst_3432_);
lean_inc_ref(v_inst_3431_);
lean_inc_ref(v_inst_3430_);
lean_inc_ref(v_inst_3429_);
lean_inc_ref(v_inst_3428_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3447_, 0, v_view_3438_);
lean_closure_set(v___f_3447_, 1, v_n_u2081_3440_);
lean_closure_set(v___f_3447_, 2, v_inst_3428_);
lean_closure_set(v___f_3447_, 3, v_inst_3429_);
lean_closure_set(v___f_3447_, 4, v_inst_3430_);
lean_closure_set(v___f_3447_, 5, v_inst_3431_);
lean_closure_set(v___f_3447_, 6, v_inst_3432_);
lean_closure_set(v___f_3447_, 7, v_inst_3433_);
lean_closure_set(v___f_3447_, 8, v_n_u2080_3434_);
lean_closure_set(v___f_3447_, 9, v_filter_3437_);
lean_closure_set(v___f_3447_, 10, v_toPure_3445_);
v___x_3448_ = lean_box(v_allowHorizAliases_3436_);
v___f_3449_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_3449_, 0, v_toPure_3445_);
lean_closure_set(v___f_3449_, 1, v_inst_3428_);
lean_closure_set(v___f_3449_, 2, v_inst_3429_);
lean_closure_set(v___f_3449_, 3, v_inst_3430_);
lean_closure_set(v___f_3449_, 4, v_inst_3431_);
lean_closure_set(v___f_3449_, 5, v_inst_3432_);
lean_closure_set(v___f_3449_, 6, v_inst_3433_);
lean_closure_set(v___f_3449_, 7, v_n_u2080_3434_);
lean_closure_set(v___f_3449_, 8, v_filter_3437_);
lean_closure_set(v___f_3449_, 9, v___x_3441_);
lean_closure_set(v___f_3449_, 10, v_toBind_3444_);
lean_closure_set(v___f_3449_, 11, v___f_3447_);
lean_closure_set(v___f_3449_, 12, v___x_3448_);
lean_closure_set(v___f_3449_, 13, v___f_3446_);
v___f_3450_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3450_, 0, v_toPure_3445_);
v___x_3451_ = lean_apply_4(v_toBind_3444_, lean_box(0), lean_box(0), v_getEnv_3443_, v___f_3450_);
v___x_3452_ = lean_apply_4(v_toBind_3444_, lean_box(0), lean_box(0), v___x_3451_, v___f_3449_);
return v___x_3452_;
}
else
{
lean_object* v_toApplicative_3453_; lean_object* v_toBind_3454_; lean_object* v_toPure_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; 
lean_dec_ref(v___x_3441_);
v_toApplicative_3453_ = lean_ctor_get(v_inst_3428_, 0);
v_toBind_3454_ = lean_ctor_get(v_inst_3428_, 1);
lean_inc(v_toBind_3454_);
v_toPure_3455_ = lean_ctor_get(v_toApplicative_3453_, 1);
lean_inc(v_toPure_3455_);
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_view_3438_);
lean_inc(v_n_u2081_3440_);
lean_inc_ref(v___x_3456_);
lean_inc(v_filter_3437_);
lean_inc(v_n_u2080_3434_);
lean_inc(v_inst_3433_);
lean_inc_ref(v_inst_3432_);
lean_inc_ref(v_inst_3431_);
lean_inc_ref(v_inst_3430_);
lean_inc_ref(v_inst_3429_);
lean_inc_ref(v_inst_3428_);
v___x_3457_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3428_, v_inst_3429_, v_inst_3430_, v_inst_3431_, v_inst_3432_, v_inst_3433_, v_n_u2080_3434_, v_filter_3437_, v___x_3456_, v_n_u2081_3440_);
v___f_3458_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3458_, 0, v_n_u2081_3440_);
lean_closure_set(v___f_3458_, 1, v_inst_3428_);
lean_closure_set(v___f_3458_, 2, v_inst_3429_);
lean_closure_set(v___f_3458_, 3, v_inst_3430_);
lean_closure_set(v___f_3458_, 4, v_inst_3431_);
lean_closure_set(v___f_3458_, 5, v_inst_3432_);
lean_closure_set(v___f_3458_, 6, v_inst_3433_);
lean_closure_set(v___f_3458_, 7, v_n_u2080_3434_);
lean_closure_set(v___f_3458_, 8, v_filter_3437_);
lean_closure_set(v___f_3458_, 9, v___x_3456_);
lean_closure_set(v___f_3458_, 10, v_toPure_3455_);
v___x_3459_ = lean_apply_4(v_toBind_3454_, lean_box(0), lean_box(0), v___x_3457_, v___f_3458_);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_n_u2080_3466_, lean_object* v_fullNames_3467_, lean_object* v_allowHorizAliases_3468_, lean_object* v_filter_3469_){
_start:
{
uint8_t v_fullNames_boxed_3470_; uint8_t v_allowHorizAliases_boxed_3471_; lean_object* v_res_3472_; 
v_fullNames_boxed_3470_ = lean_unbox(v_fullNames_3467_);
v_allowHorizAliases_boxed_3471_ = lean_unbox(v_allowHorizAliases_3468_);
v_res_3472_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3460_, v_inst_3461_, v_inst_3462_, v_inst_3463_, v_inst_3464_, v_inst_3465_, v_n_u2080_3466_, v_fullNames_boxed_3470_, v_allowHorizAliases_boxed_3471_, v_filter_3469_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_n_u2080_3480_, uint8_t v_fullNames_3481_, uint8_t v_allowHorizAliases_3482_, lean_object* v_filter_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3474_, v_inst_3475_, v_inst_3476_, v_inst_3477_, v_inst_3478_, v_inst_3479_, v_n_u2080_3480_, v_fullNames_3481_, v_allowHorizAliases_3482_, v_filter_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3485_, lean_object* v_inst_3486_, lean_object* v_inst_3487_, lean_object* v_inst_3488_, lean_object* v_inst_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_n_u2080_3492_, lean_object* v_fullNames_3493_, lean_object* v_allowHorizAliases_3494_, lean_object* v_filter_3495_){
_start:
{
uint8_t v_fullNames_boxed_3496_; uint8_t v_allowHorizAliases_boxed_3497_; lean_object* v_res_3498_; 
v_fullNames_boxed_3496_ = lean_unbox(v_fullNames_3493_);
v_allowHorizAliases_boxed_3497_ = lean_unbox(v_allowHorizAliases_3494_);
v_res_3498_ = l_Lean_unresolveNameGlobal_x3f(v_m_3485_, v_inst_3486_, v_inst_3487_, v_inst_3488_, v_inst_3489_, v_inst_3490_, v_inst_3491_, v_n_u2080_3492_, v_fullNames_boxed_3496_, v_allowHorizAliases_boxed_3497_, v_filter_3495_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3499_, lean_object* v_n_u2080_3500_, lean_object* v_n_x3f_3501_){
_start:
{
if (lean_obj_tag(v_n_x3f_3501_) == 0)
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_apply_2(v_toPure_3499_, lean_box(0), v_n_u2080_3500_);
return v___x_3502_;
}
else
{
lean_object* v_val_3503_; lean_object* v___x_3504_; 
lean_dec(v_n_u2080_3500_);
v_val_3503_ = lean_ctor_get(v_n_x3f_3501_, 0);
lean_inc(v_val_3503_);
lean_dec_ref_known(v_n_x3f_3501_, 1);
v___x_3504_ = lean_apply_2(v_toPure_3499_, lean_box(0), v_val_3503_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3505_, lean_object* v_inst_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_n_u2080_3511_, uint8_t v_fullNames_3512_, uint8_t v_allowHorizAliases_3513_, lean_object* v_filter_3514_){
_start:
{
lean_object* v_toApplicative_3515_; lean_object* v_toBind_3516_; lean_object* v_toPure_3517_; lean_object* v___x_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; 
v_toApplicative_3515_ = lean_ctor_get(v_inst_3505_, 0);
v_toBind_3516_ = lean_ctor_get(v_inst_3505_, 1);
lean_inc(v_toBind_3516_);
v_toPure_3517_ = lean_ctor_get(v_toApplicative_3515_, 1);
lean_inc(v_toPure_3517_);
lean_inc(v_n_u2080_3511_);
v___x_3518_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3505_, v_inst_3506_, v_inst_3507_, v_inst_3508_, v_inst_3509_, v_inst_3510_, v_n_u2080_3511_, v_fullNames_3512_, v_allowHorizAliases_3513_, v_filter_3514_);
v___f_3519_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3519_, 0, v_toPure_3517_);
lean_closure_set(v___f_3519_, 1, v_n_u2080_3511_);
v___x_3520_ = lean_apply_4(v_toBind_3516_, lean_box(0), lean_box(0), v___x_3518_, v___f_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_n_u2080_3527_, lean_object* v_fullNames_3528_, lean_object* v_allowHorizAliases_3529_, lean_object* v_filter_3530_){
_start:
{
uint8_t v_fullNames_boxed_3531_; uint8_t v_allowHorizAliases_boxed_3532_; lean_object* v_res_3533_; 
v_fullNames_boxed_3531_ = lean_unbox(v_fullNames_3528_);
v_allowHorizAliases_boxed_3532_ = lean_unbox(v_allowHorizAliases_3529_);
v_res_3533_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3521_, v_inst_3522_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v_inst_3526_, v_n_u2080_3527_, v_fullNames_boxed_3531_, v_allowHorizAliases_boxed_3532_, v_filter_3530_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_n_u2080_3541_, uint8_t v_fullNames_3542_, uint8_t v_allowHorizAliases_3543_, lean_object* v_filter_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3535_, v_inst_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_inst_3540_, v_n_u2080_3541_, v_fullNames_3542_, v_allowHorizAliases_3543_, v_filter_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3546_, lean_object* v_inst_3547_, lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_n_u2080_3553_, lean_object* v_fullNames_3554_, lean_object* v_allowHorizAliases_3555_, lean_object* v_filter_3556_){
_start:
{
uint8_t v_fullNames_boxed_3557_; uint8_t v_allowHorizAliases_boxed_3558_; lean_object* v_res_3559_; 
v_fullNames_boxed_3557_ = lean_unbox(v_fullNames_3554_);
v_allowHorizAliases_boxed_3558_ = lean_unbox(v_allowHorizAliases_3555_);
v_res_3559_ = l_Lean_unresolveNameGlobal(v_m_3546_, v_inst_3547_, v_inst_3548_, v_inst_3549_, v_inst_3550_, v_inst_3551_, v_inst_3552_, v_n_u2080_3553_, v_fullNames_boxed_3557_, v_allowHorizAliases_boxed_3558_, v_filter_3556_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3561_, lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_n_3569_){
_start:
{
lean_object* v_map_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_map_3570_ = lean_ctor_get(v_toFunctor_3561_, 0);
lean_inc(v_map_3570_);
lean_dec_ref(v_toFunctor_3561_);
v___x_3571_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3572_ = l_Lean_resolveLocalName___redArg(v_inst_3562_, v_inst_3563_, v_inst_3564_, v_inst_3565_, v_inst_3566_, v_inst_3567_, v_inst_3568_, v_n_3569_);
v___x_3573_ = lean_apply_4(v_map_3570_, lean_box(0), lean_box(0), v___x_3571_, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_n_u2080_3581_, uint8_t v_fullNames_3582_){
_start:
{
lean_object* v_toApplicative_3583_; lean_object* v_toFunctor_3584_; uint8_t v___x_3585_; lean_object* v___f_3586_; lean_object* v___x_3587_; 
v_toApplicative_3583_ = lean_ctor_get(v_inst_3574_, 0);
v_toFunctor_3584_ = lean_ctor_get(v_toApplicative_3583_, 0);
v___x_3585_ = 0;
lean_inc(v_inst_3579_);
lean_inc_ref(v_inst_3578_);
lean_inc_ref(v_inst_3577_);
lean_inc_ref(v_inst_3576_);
lean_inc_ref(v_inst_3575_);
lean_inc_ref(v_inst_3574_);
lean_inc_ref(v_toFunctor_3584_);
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3586_, 0, v_toFunctor_3584_);
lean_closure_set(v___f_3586_, 1, v_inst_3574_);
lean_closure_set(v___f_3586_, 2, v_inst_3575_);
lean_closure_set(v___f_3586_, 3, v_inst_3576_);
lean_closure_set(v___f_3586_, 4, v_inst_3577_);
lean_closure_set(v___f_3586_, 5, v_inst_3578_);
lean_closure_set(v___f_3586_, 6, v_inst_3579_);
lean_closure_set(v___f_3586_, 7, v_inst_3580_);
v___x_3587_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3574_, v_inst_3575_, v_inst_3576_, v_inst_3577_, v_inst_3578_, v_inst_3579_, v_n_u2080_3581_, v_fullNames_3582_, v___x_3585_, v___f_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_n_u2080_3595_, lean_object* v_fullNames_3596_){
_start:
{
uint8_t v_fullNames_boxed_3597_; lean_object* v_res_3598_; 
v_fullNames_boxed_3597_ = lean_unbox(v_fullNames_3596_);
v_res_3598_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3588_, v_inst_3589_, v_inst_3590_, v_inst_3591_, v_inst_3592_, v_inst_3593_, v_inst_3594_, v_n_u2080_3595_, v_fullNames_boxed_3597_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_n_u2080_3607_, uint8_t v_fullNames_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3600_, v_inst_3601_, v_inst_3602_, v_inst_3603_, v_inst_3604_, v_inst_3605_, v_inst_3606_, v_n_u2080_3607_, v_fullNames_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_n_u2080_3618_, lean_object* v_fullNames_3619_){
_start:
{
uint8_t v_fullNames_boxed_3620_; lean_object* v_res_3621_; 
v_fullNames_boxed_3620_ = lean_unbox(v_fullNames_3619_);
v_res_3621_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_n_u2080_3618_, v_fullNames_boxed_3620_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3622_, lean_object* v_inst_3623_, lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_n_u2080_3629_, uint8_t v_fullNames_3630_){
_start:
{
lean_object* v_toApplicative_3631_; lean_object* v_toBind_3632_; lean_object* v_toPure_3633_; lean_object* v___x_3634_; lean_object* v___f_3635_; lean_object* v___x_3636_; 
v_toApplicative_3631_ = lean_ctor_get(v_inst_3622_, 0);
v_toBind_3632_ = lean_ctor_get(v_inst_3622_, 1);
lean_inc(v_toBind_3632_);
v_toPure_3633_ = lean_ctor_get(v_toApplicative_3631_, 1);
lean_inc(v_toPure_3633_);
lean_inc(v_n_u2080_3629_);
v___x_3634_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3622_, v_inst_3623_, v_inst_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_n_u2080_3629_, v_fullNames_3630_);
v___f_3635_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3635_, 0, v_toPure_3633_);
lean_closure_set(v___f_3635_, 1, v_n_u2080_3629_);
v___x_3636_ = lean_apply_4(v_toBind_3632_, lean_box(0), lean_box(0), v___x_3634_, v___f_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_n_u2080_3644_, lean_object* v_fullNames_3645_){
_start:
{
uint8_t v_fullNames_boxed_3646_; lean_object* v_res_3647_; 
v_fullNames_boxed_3646_ = lean_unbox(v_fullNames_3645_);
v_res_3647_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3637_, v_inst_3638_, v_inst_3639_, v_inst_3640_, v_inst_3641_, v_inst_3642_, v_inst_3643_, v_n_u2080_3644_, v_fullNames_boxed_3646_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3648_, lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_inst_3651_, lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_inst_3654_, lean_object* v_inst_3655_, lean_object* v_n_u2080_3656_, uint8_t v_fullNames_3657_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3649_, v_inst_3650_, v_inst_3651_, v_inst_3652_, v_inst_3653_, v_inst_3654_, v_inst_3655_, v_n_u2080_3656_, v_fullNames_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3659_, lean_object* v_inst_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_inst_3666_, lean_object* v_n_u2080_3667_, lean_object* v_fullNames_3668_){
_start:
{
uint8_t v_fullNames_boxed_3669_; lean_object* v_res_3670_; 
v_fullNames_boxed_3669_ = lean_unbox(v_fullNames_3668_);
v_res_3670_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3659_, v_inst_3660_, v_inst_3661_, v_inst_3662_, v_inst_3663_, v_inst_3664_, v_inst_3665_, v_inst_3666_, v_n_u2080_3667_, v_fullNames_boxed_3669_);
return v_res_3670_;
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
