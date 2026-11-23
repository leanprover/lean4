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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
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
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Array_instInhabited___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef;
static const lean_string_object l_Lean_registerReservedNamePredicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "failed to register reserved name suffix predicate, this operation can only be performed during initialization"};
static const lean_object* l_Lean_registerReservedNamePredicate___closed__0 = (const lean_object*)&l_Lean_registerReservedNamePredicate___closed__0_value;
static lean_once_cell_t l_Lean_registerReservedNamePredicate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerReservedNamePredicate___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ResolveName"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 177, 204, 170, 165, 172, 163, 11)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(196, 116, 196, 114, 71, 43, 230, 17)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 182, 208, 129, 167, 183, 199, 41)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "reservedNamePredsExt"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 95, 79, 214, 117, 203, 5, 233)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_reservedNamePredsExt;
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 161, 136, 183, 131, 203, 158, 84)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 154, 217, 244, 61, 155, 3, 144)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2_));
v___x_74_ = lean_st_mk_ref(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2____boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2_();
return v_res_77_;
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__1(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_registerReservedNamePredicate___closed__0));
v___x_80_ = lean_mk_io_user_error(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object* v_isCandidate_81_, lean_object* v_isReserved_82_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_initializing();
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v_isReserved_82_);
lean_dec_ref(v_isCandidate_81_);
v___x_85_ = lean_obj_once(&l_Lean_registerReservedNamePredicate___closed__1, &l_Lean_registerReservedNamePredicate___closed__1_once, _init_l_Lean_registerReservedNamePredicate___closed__1);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_87_ = l_Lean_reservedNamePredicatesRef;
v___x_88_ = lean_st_ref_take(v___x_87_);
lean_inc_ref(v_isReserved_82_);
v___x_89_ = lean_array_push(v___x_88_, v_isReserved_82_);
v___x_90_ = lean_st_ref_put(v___x_87_, v___x_89_);
v___x_91_ = l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef;
v___x_92_ = lean_st_ref_take(v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_isCandidate_81_);
lean_ctor_set(v___x_93_, 1, v_isReserved_82_);
v___x_94_ = lean_array_push(v___x_92_, v___x_93_);
v___x_95_ = lean_st_ref_put(v___x_91_, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object* v_isCandidate_97_, lean_object* v_isReserved_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_registerReservedNamePredicate(v_isCandidate_97_, v_isReserved_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(lean_object* v___x_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_st_ref_get(v___x_101_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object* v___x_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(v___x_105_);
lean_dec(v___x_105_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___f_109_; 
v___x_108_ = l_Lean_reservedNamePredicatesRef;
v___f_109_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_109_, 0, v___x_108_);
return v___f_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; 
v___f_116_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_box(2);
v___x_119_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_));
v___x_120_ = 0;
v___x_121_ = 1;
v___x_122_ = l_Lean_registerEnvExtension___redArg(v___f_116_, v___x_117_, v___x_118_, v___x_119_, v___x_120_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2____boxed(lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(lean_object* v___x_125_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_st_ref_get(v___x_125_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object* v___x_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(v___x_129_);
lean_dec(v___x_129_);
return v_res_131_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_132_; lean_object* v___f_133_; 
v___x_132_ = l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef;
v___f_133_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_133_, 0, v___x_132_);
return v___f_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; 
v___f_156_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_box(2);
v___x_159_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_));
v___x_160_ = 0;
v___x_161_ = 1;
v___x_162_ = l_Lean_registerEnvExtension___redArg(v___f_156_, v___x_157_, v___x_158_, v___x_159_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_();
return v_res_164_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_env_165_, lean_object* v_name_166_, lean_object* v_as_167_, size_t v_i_168_, size_t v_stop_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = lean_usize_dec_eq(v_i_168_, v_stop_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_154__overap_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_154__overap_171_ = lean_array_uget_borrowed(v_as_167_, v_i_168_);
lean_inc(v___x_154__overap_171_);
lean_inc(v_name_166_);
lean_inc_ref(v_env_165_);
v___x_172_ = lean_apply_2(v___x_154__overap_171_, v_env_165_, v_name_166_);
v___x_173_ = lean_unbox(v___x_172_);
if (v___x_173_ == 0)
{
size_t v___x_174_; size_t v___x_175_; 
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_i_168_, v___x_174_);
v_i_168_ = v___x_175_;
goto _start;
}
else
{
uint8_t v___x_177_; 
lean_dec(v_name_166_);
lean_dec_ref(v_env_165_);
v___x_177_ = lean_unbox(v___x_172_);
return v___x_177_;
}
}
else
{
uint8_t v___x_178_; 
lean_dec(v_name_166_);
lean_dec_ref(v_env_165_);
v___x_178_ = 0;
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_env_179_, lean_object* v_name_180_, lean_object* v_as_181_, lean_object* v_i_182_, lean_object* v_stop_183_){
_start:
{
size_t v_i_boxed_184_; size_t v_stop_boxed_185_; uint8_t v_res_186_; lean_object* v_r_187_; 
v_i_boxed_184_ = lean_unbox_usize(v_i_182_);
lean_dec(v_i_182_);
v_stop_boxed_185_ = lean_unbox_usize(v_stop_183_);
lean_dec(v_stop_183_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_179_, v_name_180_, v_as_181_, v_i_boxed_184_, v_stop_boxed_185_);
lean_dec_ref(v_as_181_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0(void){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Array_instInhabited___redArg();
return v___x_188_;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* v_env_189_, lean_object* v_name_190_){
_start:
{
lean_object* v___x_191_; lean_object* v_asyncMode_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_191_ = l_Lean_reservedNamePredicatesExt;
v_asyncMode_192_ = lean_ctor_get(v___x_191_, 2);
v___x_193_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_194_ = lean_box(0);
v___x_195_ = 0;
lean_inc_ref(v_env_189_);
v___x_196_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_193_, v___x_191_, v_env_189_, v_asyncMode_192_, v___x_194_, v___x_195_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_array_get_size(v___x_196_);
v___x_199_ = lean_nat_dec_lt(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec(v___x_196_);
lean_dec(v_name_190_);
lean_dec_ref(v_env_189_);
return v___x_199_;
}
else
{
if (v___x_199_ == 0)
{
lean_dec(v___x_196_);
lean_dec(v_name_190_);
lean_dec_ref(v_env_189_);
return v___x_199_;
}
else
{
size_t v___x_200_; size_t v___x_201_; uint8_t v___x_202_; 
v___x_200_ = ((size_t)0ULL);
v___x_201_ = lean_usize_of_nat(v___x_198_);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_189_, v_name_190_, v___x_196_, v___x_200_, v___x_201_);
lean_dec(v___x_196_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_203_, lean_object* v_name_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = lean_is_reserved_name(v_env_203_, v_name_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_ks_211_; lean_object* v_vs_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_236_; 
v_ks_211_ = lean_ctor_get(v_x_207_, 0);
v_vs_212_ = lean_ctor_get(v_x_207_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_236_ == 0)
{
v___x_214_ = v_x_207_;
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_vs_212_);
lean_inc(v_ks_211_);
lean_dec(v_x_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_get_size(v_ks_211_);
v___x_217_ = lean_nat_dec_lt(v_x_208_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec(v_x_208_);
v___x_218_ = lean_array_push(v_ks_211_, v_x_209_);
v___x_219_ = lean_array_push(v_vs_212_, v_x_210_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_219_);
lean_ctor_set(v___x_214_, 0, v___x_218_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
else
{
lean_object* v_k_x27_223_; uint8_t v___x_224_; 
v_k_x27_223_ = lean_array_fget_borrowed(v_ks_211_, v_x_208_);
v___x_224_ = lean_name_eq(v_x_209_, v_k_x27_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; 
if (v_isShared_215_ == 0)
{
v___x_226_ = v___x_214_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_ks_211_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_vs_212_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_x_208_, v___x_227_);
lean_dec(v_x_208_);
v_x_207_ = v___x_226_;
v_x_208_ = v___x_228_;
goto _start;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = lean_array_fset(v_ks_211_, v_x_208_, v_x_209_);
v___x_232_ = lean_array_fset(v_vs_212_, v_x_208_, v_x_210_);
lean_dec(v_x_208_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_232_);
lean_ctor_set(v___x_214_, 0, v___x_231_);
v___x_234_ = v___x_214_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_237_, lean_object* v_k_238_, lean_object* v_v_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_237_, v___x_240_, v_k_238_, v_v_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_243_, size_t v_x_244_, size_t v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v_es_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v_j_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_es_248_ = lean_ctor_get(v_x_243_, 0);
v___x_249_ = ((size_t)31ULL);
v___x_250_ = lean_usize_land(v_x_244_, v___x_249_);
v_j_251_ = lean_usize_to_nat(v___x_250_);
v___x_252_ = lean_array_get_size(v_es_248_);
v___x_253_ = lean_nat_dec_lt(v_j_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec(v_j_251_);
lean_dec(v_x_247_);
lean_dec(v_x_246_);
return v_x_243_;
}
else
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_292_; 
lean_inc_ref(v_es_248_);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_x_243_, 0);
lean_dec(v_unused_293_);
v___x_255_ = v_x_243_;
v_isShared_256_ = v_isSharedCheck_292_;
goto v_resetjp_254_;
}
else
{
lean_dec(v_x_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_292_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v_v_257_; lean_object* v___x_258_; lean_object* v_xs_x27_259_; lean_object* v___y_261_; 
v_v_257_ = lean_array_fget(v_es_248_, v_j_251_);
v___x_258_ = lean_box(0);
v_xs_x27_259_ = lean_array_fset(v_es_248_, v_j_251_, v___x_258_);
switch(lean_obj_tag(v_v_257_))
{
case 0:
{
lean_object* v_key_266_; lean_object* v_val_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_key_266_ = lean_ctor_get(v_v_257_, 0);
v_val_267_ = lean_ctor_get(v_v_257_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_v_257_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v_v_257_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_val_267_);
lean_inc(v_key_266_);
lean_dec(v_v_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
uint8_t v___x_271_; 
v___x_271_ = lean_name_eq(v_x_246_, v_key_266_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_del_object(v___x_269_);
v___x_272_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_266_, v_val_267_, v_x_246_, v_x_247_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___y_261_ = v___x_273_;
goto v___jp_260_;
}
else
{
lean_object* v___x_275_; 
lean_dec(v_val_267_);
lean_dec(v_key_266_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_x_247_);
lean_ctor_set(v___x_269_, 0, v_x_246_);
v___x_275_ = v___x_269_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_x_246_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_x_247_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
v___y_261_ = v___x_275_;
goto v___jp_260_;
}
}
}
}
case 1:
{
lean_object* v_node_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_290_; 
v_node_278_ = lean_ctor_get(v_v_257_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_v_257_);
if (v_isSharedCheck_290_ == 0)
{
v___x_280_ = v_v_257_;
v_isShared_281_ = v_isSharedCheck_290_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_node_278_);
lean_dec(v_v_257_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_290_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_282_ = ((size_t)5ULL);
v___x_283_ = lean_usize_shift_right(v_x_244_, v___x_282_);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_add(v_x_245_, v___x_284_);
v___x_286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_278_, v___x_283_, v___x_285_, v_x_246_, v_x_247_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_286_);
v___x_288_ = v___x_280_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
v___y_261_ = v___x_288_;
goto v___jp_260_;
}
}
}
default: 
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_x_246_);
lean_ctor_set(v___x_291_, 1, v_x_247_);
v___y_261_ = v___x_291_;
goto v___jp_260_;
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_array_fset(v_xs_x27_259_, v_j_251_, v___y_261_);
lean_dec(v_j_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_262_);
v___x_264_ = v___x_255_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
else
{
lean_object* v_ks_294_; lean_object* v_vs_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_313_; 
v_ks_294_ = lean_ctor_get(v_x_243_, 0);
v_vs_295_ = lean_ctor_get(v_x_243_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_313_ == 0)
{
v___x_297_ = v_x_243_;
v_isShared_298_ = v_isSharedCheck_313_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_vs_295_);
lean_inc(v_ks_294_);
lean_dec(v_x_243_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_313_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_ks_294_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_vs_295_);
v___x_300_ = v_reuseFailAlloc_312_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v_newNode_301_; size_t v___x_302_; uint8_t v___x_303_; 
v_newNode_301_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_300_, v_x_246_, v_x_247_);
v___x_302_ = ((size_t)7ULL);
v___x_303_ = lean_usize_dec_le(v___x_302_, v_x_245_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_301_);
v___x_305_ = lean_unsigned_to_nat(4u);
v___x_306_ = lean_nat_dec_lt(v___x_304_, v___x_305_);
lean_dec(v___x_304_);
if (v___x_306_ == 0)
{
lean_object* v_ks_307_; lean_object* v_vs_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_ks_307_ = lean_ctor_get(v_newNode_301_, 0);
lean_inc_ref(v_ks_307_);
v_vs_308_ = lean_ctor_get(v_newNode_301_, 1);
lean_inc_ref(v_vs_308_);
lean_dec_ref(v_newNode_301_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_245_, v_ks_307_, v_vs_308_, v___x_309_, v___x_310_);
lean_dec_ref(v_vs_308_);
lean_dec_ref(v_ks_307_);
return v___x_311_;
}
else
{
return v_newNode_301_;
}
}
else
{
return v_newNode_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_314_, lean_object* v_keys_315_, lean_object* v_vals_316_, lean_object* v_i_317_, lean_object* v_entries_318_){
_start:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_array_get_size(v_keys_315_);
v___x_320_ = lean_nat_dec_lt(v_i_317_, v___x_319_);
if (v___x_320_ == 0)
{
lean_dec(v_i_317_);
return v_entries_318_;
}
else
{
lean_object* v_k_321_; lean_object* v_v_322_; uint64_t v___y_324_; 
v_k_321_ = lean_array_fget_borrowed(v_keys_315_, v_i_317_);
v_v_322_ = lean_array_fget_borrowed(v_vals_316_, v_i_317_);
if (lean_obj_tag(v_k_321_) == 0)
{
uint64_t v___x_335_; 
v___x_335_ = 1723ULL;
v___y_324_ = v___x_335_;
goto v___jp_323_;
}
else
{
uint64_t v_hash_336_; 
v_hash_336_ = lean_ctor_get_uint64(v_k_321_, sizeof(void*)*2);
v___y_324_ = v_hash_336_;
goto v___jp_323_;
}
v___jp_323_:
{
size_t v_h_325_; size_t v___x_326_; lean_object* v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v_h_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_h_325_ = lean_uint64_to_usize(v___y_324_);
v___x_326_ = ((size_t)5ULL);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = ((size_t)1ULL);
v___x_329_ = lean_usize_sub(v_depth_314_, v___x_328_);
v___x_330_ = lean_usize_mul(v___x_326_, v___x_329_);
v_h_331_ = lean_usize_shift_right(v_h_325_, v___x_330_);
v___x_332_ = lean_nat_add(v_i_317_, v___x_327_);
lean_dec(v_i_317_);
lean_inc(v_v_322_);
lean_inc(v_k_321_);
v___x_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_318_, v_h_331_, v_depth_314_, v_k_321_, v_v_322_);
v_i_317_ = v___x_332_;
v_entries_318_ = v___x_333_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_337_, lean_object* v_keys_338_, lean_object* v_vals_339_, lean_object* v_i_340_, lean_object* v_entries_341_){
_start:
{
size_t v_depth_boxed_342_; lean_object* v_res_343_; 
v_depth_boxed_342_ = lean_unbox_usize(v_depth_337_);
lean_dec(v_depth_337_);
v_res_343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_342_, v_keys_338_, v_vals_339_, v_i_340_, v_entries_341_);
lean_dec_ref(v_vals_339_);
lean_dec_ref(v_keys_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
size_t v_x_1075__boxed_349_; size_t v_x_1076__boxed_350_; lean_object* v_res_351_; 
v_x_1075__boxed_349_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_x_1076__boxed_350_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_res_351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_344_, v_x_1075__boxed_349_, v_x_1076__boxed_350_, v_x_347_, v_x_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint64_t v___y_356_; 
if (lean_obj_tag(v_x_353_) == 0)
{
uint64_t v___x_360_; 
v___x_360_ = 1723ULL;
v___y_356_ = v___x_360_;
goto v___jp_355_;
}
else
{
uint64_t v_hash_361_; 
v_hash_361_ = lean_ctor_get_uint64(v_x_353_, sizeof(void*)*2);
v___y_356_ = v_hash_361_;
goto v___jp_355_;
}
v___jp_355_:
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_uint64_to_usize(v___y_356_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_352_, v___x_357_, v___x_358_, v_x_353_, v_x_354_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
return v_x_362_;
}
else
{
lean_object* v_key_364_; lean_object* v_value_365_; lean_object* v_tail_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_392_; 
v_key_364_ = lean_ctor_get(v_x_363_, 0);
v_value_365_ = lean_ctor_get(v_x_363_, 1);
v_tail_366_ = lean_ctor_get(v_x_363_, 2);
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_363_);
if (v_isSharedCheck_392_ == 0)
{
v___x_368_ = v_x_363_;
v_isShared_369_ = v_isSharedCheck_392_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_tail_366_);
lean_inc(v_value_365_);
lean_inc(v_key_364_);
lean_dec(v_x_363_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_392_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; uint64_t v___y_372_; 
v___x_370_ = lean_array_get_size(v_x_362_);
if (lean_obj_tag(v_key_364_) == 0)
{
uint64_t v___x_390_; 
v___x_390_ = 1723ULL;
v___y_372_ = v___x_390_;
goto v___jp_371_;
}
else
{
uint64_t v_hash_391_; 
v_hash_391_ = lean_ctor_get_uint64(v_key_364_, sizeof(void*)*2);
v___y_372_ = v_hash_391_;
goto v___jp_371_;
}
v___jp_371_:
{
uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v_fold_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_373_ = 32ULL;
v___x_374_ = lean_uint64_shift_right(v___y_372_, v___x_373_);
v_fold_375_ = lean_uint64_xor(v___y_372_, v___x_374_);
v___x_376_ = 16ULL;
v___x_377_ = lean_uint64_shift_right(v_fold_375_, v___x_376_);
v___x_378_ = lean_uint64_xor(v_fold_375_, v___x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = lean_usize_of_nat(v___x_370_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_sub(v___x_380_, v___x_381_);
v___x_383_ = lean_usize_land(v___x_379_, v___x_382_);
v___x_384_ = lean_array_uget_borrowed(v_x_362_, v___x_383_);
lean_inc(v___x_384_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 2, v___x_384_);
v___x_386_ = v___x_368_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_key_364_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_value_365_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_384_);
v___x_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
v___x_387_ = lean_array_uset(v_x_362_, v___x_383_, v___x_386_);
v_x_362_ = v___x_387_;
v_x_363_ = v_tail_366_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_393_, lean_object* v_source_394_, lean_object* v_target_395_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_array_get_size(v_source_394_);
v___x_397_ = lean_nat_dec_lt(v_i_393_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec_ref(v_source_394_);
lean_dec(v_i_393_);
return v_target_395_;
}
else
{
lean_object* v_es_398_; lean_object* v___x_399_; lean_object* v_source_400_; lean_object* v_target_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_es_398_ = lean_array_fget(v_source_394_, v_i_393_);
v___x_399_ = lean_box(0);
v_source_400_ = lean_array_fset(v_source_394_, v_i_393_, v___x_399_);
v_target_401_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_395_, v_es_398_);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_add(v_i_393_, v___x_402_);
lean_dec(v_i_393_);
v_i_393_ = v___x_403_;
v_source_394_ = v_source_400_;
v_target_395_ = v_target_401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_nbuckets_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_406_ = lean_array_get_size(v_data_405_);
v___x_407_ = lean_unsigned_to_nat(2u);
v_nbuckets_408_ = lean_nat_mul(v___x_406_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_box(0);
v___x_411_ = lean_mk_array(v_nbuckets_408_, v___x_410_);
v___x_412_ = lean_array_propagate_mark(v_data_405_, v___x_411_);
v___x_413_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_409_, v_data_405_, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_414_, lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
else
{
lean_object* v_key_417_; lean_object* v_tail_418_; uint8_t v___x_419_; 
v_key_417_ = lean_ctor_get(v_x_415_, 0);
v_tail_418_ = lean_ctor_get(v_x_415_, 2);
v___x_419_ = lean_name_eq(v_key_417_, v_a_414_);
if (v___x_419_ == 0)
{
v_x_415_ = v_tail_418_;
goto _start;
}
else
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_421_, lean_object* v_x_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_421_, v_x_422_);
lean_dec(v_x_422_);
lean_dec(v_a_421_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_425_, lean_object* v_b_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_dec(v_b_426_);
lean_dec(v_a_425_);
return v_x_427_;
}
else
{
lean_object* v_key_428_; lean_object* v_value_429_; lean_object* v_tail_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_442_; 
v_key_428_ = lean_ctor_get(v_x_427_, 0);
v_value_429_ = lean_ctor_get(v_x_427_, 1);
v_tail_430_ = lean_ctor_get(v_x_427_, 2);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_427_);
if (v_isSharedCheck_442_ == 0)
{
v___x_432_ = v_x_427_;
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_tail_430_);
lean_inc(v_value_429_);
lean_inc(v_key_428_);
lean_dec(v_x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; 
v___x_434_ = lean_name_eq(v_key_428_, v_a_425_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_425_, v_b_426_, v_tail_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 2, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_key_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_value_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
lean_object* v___x_440_; 
lean_dec(v_value_429_);
lean_dec(v_key_428_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_b_426_);
lean_ctor_set(v___x_432_, 0, v_a_425_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_425_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_b_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_tail_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_443_, lean_object* v_a_444_, lean_object* v_b_445_){
_start:
{
lean_object* v_size_446_; lean_object* v_buckets_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_493_; 
v_size_446_ = lean_ctor_get(v_m_443_, 0);
v_buckets_447_ = lean_ctor_get(v_m_443_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_m_443_);
if (v_isSharedCheck_493_ == 0)
{
v___x_449_ = v_m_443_;
v_isShared_450_ = v_isSharedCheck_493_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_buckets_447_);
lean_inc(v_size_446_);
lean_dec(v_m_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_493_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; uint64_t v___y_453_; 
v___x_451_ = lean_array_get_size(v_buckets_447_);
if (lean_obj_tag(v_a_444_) == 0)
{
uint64_t v___x_491_; 
v___x_491_ = 1723ULL;
v___y_453_ = v___x_491_;
goto v___jp_452_;
}
else
{
uint64_t v_hash_492_; 
v_hash_492_ = lean_ctor_get_uint64(v_a_444_, sizeof(void*)*2);
v___y_453_ = v_hash_492_;
goto v___jp_452_;
}
v___jp_452_:
{
uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v_fold_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v_bkt_465_; uint8_t v___x_466_; 
v___x_454_ = 32ULL;
v___x_455_ = lean_uint64_shift_right(v___y_453_, v___x_454_);
v_fold_456_ = lean_uint64_xor(v___y_453_, v___x_455_);
v___x_457_ = 16ULL;
v___x_458_ = lean_uint64_shift_right(v_fold_456_, v___x_457_);
v___x_459_ = lean_uint64_xor(v_fold_456_, v___x_458_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = lean_usize_of_nat(v___x_451_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_sub(v___x_461_, v___x_462_);
v___x_464_ = lean_usize_land(v___x_460_, v___x_463_);
v_bkt_465_ = lean_array_uget_borrowed(v_buckets_447_, v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_444_, v_bkt_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v_size_x27_468_; lean_object* v___x_469_; lean_object* v_buckets_x27_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v_size_x27_468_ = lean_nat_add(v_size_446_, v___x_467_);
lean_dec(v_size_446_);
lean_inc(v_bkt_465_);
v___x_469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_469_, 0, v_a_444_);
lean_ctor_set(v___x_469_, 1, v_b_445_);
lean_ctor_set(v___x_469_, 2, v_bkt_465_);
v_buckets_x27_470_ = lean_array_uset(v_buckets_447_, v___x_464_, v___x_469_);
v___x_471_ = lean_unsigned_to_nat(4u);
v___x_472_ = lean_nat_mul(v_size_x27_468_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(3u);
v___x_474_ = lean_nat_div(v___x_472_, v___x_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_array_get_size(v_buckets_x27_470_);
v___x_476_ = lean_nat_dec_le(v___x_474_, v___x_475_);
lean_dec(v___x_474_);
if (v___x_476_ == 0)
{
lean_object* v_val_477_; lean_object* v___x_479_; 
v_val_477_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_470_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_val_477_);
lean_ctor_set(v___x_449_, 0, v_size_x27_468_);
v___x_479_ = v___x_449_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_size_x27_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_val_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
else
{
lean_object* v___x_482_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_buckets_x27_470_);
lean_ctor_set(v___x_449_, 0, v_size_x27_468_);
v___x_482_ = v___x_449_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_size_x27_468_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_buckets_x27_470_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v___x_484_; lean_object* v_buckets_x27_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
lean_inc(v_bkt_465_);
v___x_484_ = lean_box(0);
v_buckets_x27_485_ = lean_array_uset(v_buckets_447_, v___x_464_, v___x_484_);
v___x_486_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_444_, v_b_445_, v_bkt_465_);
v___x_487_ = lean_array_uset(v_buckets_x27_485_, v___x_464_, v___x_486_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_487_);
v___x_489_ = v___x_449_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_size_446_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_stage_u2081_497_; 
v_stage_u2081_497_ = lean_ctor_get_uint8(v_x_494_, sizeof(void*)*2);
if (v_stage_u2081_497_ == 0)
{
lean_object* v_map_u2081_498_; lean_object* v_map_u2082_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_map_u2081_498_ = lean_ctor_get(v_x_494_, 0);
v_map_u2082_499_ = lean_ctor_get(v_x_494_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_494_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v_x_494_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_map_u2082_499_);
lean_inc(v_map_u2081_498_);
lean_dec(v_x_494_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_499_, v_x_495_, v_x_496_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_map_u2081_498_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*2, v_stage_u2081_497_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v_map_u2081_508_; lean_object* v_map_u2082_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_517_; 
v_map_u2081_508_ = lean_ctor_get(v_x_494_, 0);
v_map_u2082_509_ = lean_ctor_get(v_x_494_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_494_);
if (v_isSharedCheck_517_ == 0)
{
v___x_511_ = v_x_494_;
v_isShared_512_ = v_isSharedCheck_517_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_map_u2082_509_);
lean_inc(v_map_u2081_508_);
lean_dec(v_x_494_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_517_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_508_, v_x_495_, v_x_496_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_map_u2082_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_516_, sizeof(void*)*2, v_stage_u2081_497_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v_key_521_; lean_object* v_value_522_; lean_object* v_tail_523_; uint8_t v___x_524_; 
v_key_521_ = lean_ctor_get(v_x_519_, 0);
v_value_522_ = lean_ctor_get(v_x_519_, 1);
v_tail_523_ = lean_ctor_get(v_x_519_, 2);
v___x_524_ = lean_name_eq(v_key_521_, v_a_518_);
if (v___x_524_ == 0)
{
v_x_519_ = v_tail_523_;
goto _start;
}
else
{
lean_object* v___x_526_; 
lean_inc(v_value_522_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_value_522_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_527_, v_x_528_);
lean_dec(v_x_528_);
lean_dec(v_a_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_buckets_532_; lean_object* v___x_533_; uint64_t v___y_535_; 
v_buckets_532_ = lean_ctor_get(v_m_530_, 1);
v___x_533_ = lean_array_get_size(v_buckets_532_);
if (lean_obj_tag(v_a_531_) == 0)
{
uint64_t v___x_549_; 
v___x_549_ = 1723ULL;
v___y_535_ = v___x_549_;
goto v___jp_534_;
}
else
{
uint64_t v_hash_550_; 
v_hash_550_ = lean_ctor_get_uint64(v_a_531_, sizeof(void*)*2);
v___y_535_ = v_hash_550_;
goto v___jp_534_;
}
v___jp_534_:
{
uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v_fold_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_536_ = 32ULL;
v___x_537_ = lean_uint64_shift_right(v___y_535_, v___x_536_);
v_fold_538_ = lean_uint64_xor(v___y_535_, v___x_537_);
v___x_539_ = 16ULL;
v___x_540_ = lean_uint64_shift_right(v_fold_538_, v___x_539_);
v___x_541_ = lean_uint64_xor(v_fold_538_, v___x_540_);
v___x_542_ = lean_uint64_to_usize(v___x_541_);
v___x_543_ = lean_usize_of_nat(v___x_533_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_sub(v___x_543_, v___x_544_);
v___x_546_ = lean_usize_land(v___x_542_, v___x_545_);
v___x_547_ = lean_array_uget_borrowed(v_buckets_532_, v___x_546_);
v___x_548_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_531_, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_m_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_554_, lean_object* v_vals_555_, lean_object* v_i_556_, lean_object* v_k_557_){
_start:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_array_get_size(v_keys_554_);
v___x_559_ = lean_nat_dec_lt(v_i_556_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec(v_i_556_);
v___x_560_ = lean_box(0);
return v___x_560_;
}
else
{
lean_object* v_k_x27_561_; uint8_t v___x_562_; 
v_k_x27_561_ = lean_array_fget_borrowed(v_keys_554_, v_i_556_);
v___x_562_ = lean_name_eq(v_k_557_, v_k_x27_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_i_556_, v___x_563_);
lean_dec(v_i_556_);
v_i_556_ = v___x_564_;
goto _start;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_array_fget_borrowed(v_vals_555_, v_i_556_);
lean_dec(v_i_556_);
lean_inc(v___x_566_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_568_, lean_object* v_vals_569_, lean_object* v_i_570_, lean_object* v_k_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_568_, v_vals_569_, v_i_570_, v_k_571_);
lean_dec(v_k_571_);
lean_dec_ref(v_vals_569_);
lean_dec_ref(v_keys_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_573_, size_t v_x_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v_es_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v_j_580_; lean_object* v___x_581_; 
v_es_576_ = lean_ctor_get(v_x_573_, 0);
v___x_577_ = lean_box(2);
v___x_578_ = ((size_t)31ULL);
v___x_579_ = lean_usize_land(v_x_574_, v___x_578_);
v_j_580_ = lean_usize_to_nat(v___x_579_);
v___x_581_ = lean_array_get_borrowed(v___x_577_, v_es_576_, v_j_580_);
lean_dec(v_j_580_);
switch(lean_obj_tag(v___x_581_))
{
case 0:
{
lean_object* v_key_582_; lean_object* v_val_583_; uint8_t v___x_584_; 
v_key_582_ = lean_ctor_get(v___x_581_, 0);
v_val_583_ = lean_ctor_get(v___x_581_, 1);
v___x_584_ = lean_name_eq(v_x_575_, v_key_582_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
lean_object* v___x_586_; 
lean_inc(v_val_583_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v_val_583_);
return v___x_586_;
}
}
case 1:
{
lean_object* v_node_587_; size_t v___x_588_; size_t v___x_589_; 
v_node_587_ = lean_ctor_get(v___x_581_, 0);
v___x_588_ = ((size_t)5ULL);
v___x_589_ = lean_usize_shift_right(v_x_574_, v___x_588_);
v_x_573_ = v_node_587_;
v_x_574_ = v___x_589_;
goto _start;
}
default: 
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
return v___x_591_;
}
}
}
else
{
lean_object* v_ks_592_; lean_object* v_vs_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_ks_592_ = lean_ctor_get(v_x_573_, 0);
v_vs_593_ = lean_ctor_get(v_x_573_, 1);
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_592_, v_vs_593_, v___x_594_, v_x_575_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
size_t v_x_1579__boxed_599_; lean_object* v_res_600_; 
v_x_1579__boxed_599_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_596_, v_x_1579__boxed_599_, v_x_598_);
lean_dec(v_x_598_);
lean_dec_ref(v_x_596_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
uint64_t v___y_604_; 
if (lean_obj_tag(v_x_602_) == 0)
{
uint64_t v___x_607_; 
v___x_607_ = 1723ULL;
v___y_604_ = v___x_607_;
goto v___jp_603_;
}
else
{
uint64_t v_hash_608_; 
v_hash_608_ = lean_ctor_get_uint64(v_x_602_, sizeof(void*)*2);
v___y_604_ = v_hash_608_;
goto v___jp_603_;
}
v___jp_603_:
{
size_t v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_uint64_to_usize(v___y_604_);
v___x_606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_601_, v___x_605_, v_x_602_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_609_, v_x_610_);
lean_dec(v_x_610_);
lean_dec_ref(v_x_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
uint8_t v_stage_u2081_614_; 
v_stage_u2081_614_ = lean_ctor_get_uint8(v_x_612_, sizeof(void*)*2);
if (v_stage_u2081_614_ == 0)
{
lean_object* v_map_u2081_615_; lean_object* v_map_u2082_616_; lean_object* v___x_617_; 
v_map_u2081_615_ = lean_ctor_get(v_x_612_, 0);
v_map_u2082_616_ = lean_ctor_get(v_x_612_, 1);
v___x_617_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_616_, v_x_613_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_615_, v_x_613_);
return v___x_618_;
}
else
{
return v___x_617_;
}
}
else
{
lean_object* v_map_u2081_619_; lean_object* v___x_620_; 
v_map_u2081_619_ = lean_ctor_get(v_x_612_, 0);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_619_, v_x_613_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_621_, v_x_622_);
lean_dec(v_x_622_);
lean_dec_ref(v_x_621_);
return v_res_623_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
uint8_t v___x_626_; 
v___x_626_ = 0;
return v___x_626_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; uint8_t v___x_629_; 
v_head_627_ = lean_ctor_get(v_x_625_, 0);
v_tail_628_ = lean_ctor_get(v_x_625_, 1);
v___x_629_ = lean_name_eq(v_a_624_, v_head_627_);
if (v___x_629_ == 0)
{
v_x_625_ = v_tail_628_;
goto _start;
}
else
{
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_631_, v_x_632_);
lean_dec(v_x_632_);
lean_dec(v_a_631_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_635_, lean_object* v_e_636_){
_start:
{
lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_654_; 
v_fst_637_ = lean_ctor_get(v_e_636_, 0);
v_snd_638_ = lean_ctor_get(v_e_636_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_e_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_640_ = v_e_636_;
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_inc(v_fst_637_);
lean_dec(v_e_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_635_, v_fst_637_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_box(0);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 1);
lean_ctor_set(v___x_640_, 1, v___x_643_);
lean_ctor_set(v___x_640_, 0, v_snd_638_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_snd_638_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_635_, v_fst_637_, v___x_645_);
return v___x_646_;
}
}
else
{
lean_object* v_val_648_; uint8_t v___x_649_; 
v_val_648_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_642_, 1);
v___x_649_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_638_, v_val_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_651_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 1);
lean_ctor_set(v___x_640_, 1, v_val_648_);
lean_ctor_set(v___x_640_, 0, v_snd_638_);
v___x_651_ = v___x_640_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_snd_638_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_val_648_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_635_, v_fst_637_, v___x_651_);
return v___x_652_;
}
}
else
{
lean_dec(v_val_648_);
lean_del_object(v___x_640_);
lean_dec(v_snd_638_);
lean_dec(v_fst_637_);
return v_s_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_659_, v_x_660_, v_x_661_);
lean_dec(v_x_661_);
lean_dec_ref(v_x_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_664_, v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_669_, v_x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_672_, v_x_673_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_x_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_676_, lean_object* v_m_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_677_, v_a_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_680_, lean_object* v_m_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_680_, v_m_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_m_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_685_, v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_689_, lean_object* v_m_690_, lean_object* v_a_691_, lean_object* v_b_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_690_, v_a_691_, v_b_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, size_t v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
size_t v_x_1744__boxed_703_; lean_object* v_res_704_; 
v_x_1744__boxed_703_ = lean_unbox_usize(v_x_701_);
lean_dec(v_x_701_);
v_res_704_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_699_, v_x_700_, v_x_1744__boxed_703_, v_x_702_);
lean_dec(v_x_702_);
lean_dec_ref(v_x_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_705_, lean_object* v_a_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_706_, v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_709_, lean_object* v_a_710_, lean_object* v_x_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_709_, v_a_710_, v_x_711_);
lean_dec(v_x_711_);
lean_dec(v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, size_t v_x_715_, size_t v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_714_, v_x_715_, v_x_716_, v_x_717_, v_x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
size_t v_x_1760__boxed_726_; size_t v_x_1761__boxed_727_; lean_object* v_res_728_; 
v_x_1760__boxed_726_ = lean_unbox_usize(v_x_722_);
lean_dec(v_x_722_);
v_x_1761__boxed_727_ = lean_unbox_usize(v_x_723_);
lean_dec(v_x_723_);
v_res_728_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_720_, v_x_721_, v_x_1760__boxed_726_, v_x_1761__boxed_727_, v_x_724_, v_x_725_);
return v_res_728_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_729_, lean_object* v_a_730_, lean_object* v_x_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_730_, v_x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_733_, lean_object* v_a_734_, lean_object* v_x_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_733_, v_a_734_, v_x_735_);
lean_dec(v_x_735_);
lean_dec(v_a_734_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_738_, lean_object* v_data_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_741_, lean_object* v_a_742_, lean_object* v_b_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_742_, v_b_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_746_, lean_object* v_keys_747_, lean_object* v_vals_748_, lean_object* v_heq_749_, lean_object* v_i_750_, lean_object* v_k_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_747_, v_vals_748_, v_i_750_, v_k_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_753_, lean_object* v_keys_754_, lean_object* v_vals_755_, lean_object* v_heq_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_753_, v_keys_754_, v_vals_755_, v_heq_756_, v_i_757_, v_k_758_);
lean_dec(v_k_758_);
lean_dec_ref(v_vals_755_);
lean_dec_ref(v_keys_754_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_760_, lean_object* v_n_761_, lean_object* v_k_762_, lean_object* v_v_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_761_, v_k_762_, v_v_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_765_, size_t v_depth_766_, lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_heq_769_, lean_object* v_i_770_, lean_object* v_entries_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_766_, v_keys_767_, v_vals_768_, v_i_770_, v_entries_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_773_, lean_object* v_depth_774_, lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_heq_777_, lean_object* v_i_778_, lean_object* v_entries_779_){
_start:
{
size_t v_depth_boxed_780_; lean_object* v_res_781_; 
v_depth_boxed_780_ = lean_unbox_usize(v_depth_774_);
lean_dec(v_depth_774_);
v_res_781_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_773_, v_depth_boxed_780_, v_keys_775_, v_vals_776_, v_heq_777_, v_i_778_, v_entries_779_);
lean_dec_ref(v_vals_776_);
lean_dec_ref(v_keys_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_782_, lean_object* v_i_783_, lean_object* v_source_784_, lean_object* v_target_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_783_, v_source_784_, v_target_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_788_, v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_794_, v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_797_){
_start:
{
uint8_t v_stage_u2081_798_; 
v_stage_u2081_798_ = lean_ctor_get_uint8(v_m_797_, sizeof(void*)*2);
if (v_stage_u2081_798_ == 0)
{
return v_m_797_;
}
else
{
lean_object* v_map_u2081_799_; lean_object* v_map_u2082_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_map_u2081_799_ = lean_ctor_get(v_m_797_, 0);
v_map_u2082_800_ = lean_ctor_get(v_m_797_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_m_797_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v_m_797_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_map_u2082_800_);
lean_inc(v_map_u2081_799_);
lean_dec(v_m_797_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
uint8_t v___x_804_; lean_object* v___x_806_; 
v___x_804_ = 0;
if (v_isShared_803_ == 0)
{
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_map_u2081_799_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_map_u2082_800_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*2, v___x_804_);
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_809_, lean_object* v_m_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_array_mk(v_es_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_814_, size_t v_i_815_, size_t v_stop_816_, lean_object* v_b_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = lean_usize_dec_eq(v_i_815_, v_stop_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; size_t v___x_821_; size_t v___x_822_; 
v___x_819_ = lean_array_uget_borrowed(v_as_814_, v_i_815_);
lean_inc(v___x_819_);
v___x_820_ = l_Lean_addAliasEntry(v_b_817_, v___x_819_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_815_, v___x_821_);
v_i_815_ = v___x_822_;
v_b_817_ = v___x_820_;
goto _start;
}
else
{
return v_b_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_824_, lean_object* v_i_825_, lean_object* v_stop_826_, lean_object* v_b_827_){
_start:
{
size_t v_i_boxed_828_; size_t v_stop_boxed_829_; lean_object* v_res_830_; 
v_i_boxed_828_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_stop_boxed_829_ = lean_unbox_usize(v_stop_826_);
lean_dec(v_stop_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_824_, v_i_boxed_828_, v_stop_boxed_829_, v_b_827_);
lean_dec_ref(v_as_824_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_831_, size_t v_i_832_, size_t v_stop_833_, lean_object* v_b_834_){
_start:
{
lean_object* v___y_836_; uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_eq(v_i_832_, v_stop_833_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_841_ = lean_array_uget_borrowed(v_as_831_, v_i_832_);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_array_get_size(v___x_841_);
v___x_844_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
v___y_836_ = v_b_834_;
goto v___jp_835_;
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_843_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_841_, v___x_845_, v___x_846_, v_b_834_);
v___y_836_ = v___x_847_;
goto v___jp_835_;
}
}
else
{
return v_b_834_;
}
v___jp_835_:
{
size_t v___x_837_; size_t v___x_838_; 
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_832_, v___x_837_);
v_i_832_ = v___x_838_;
v_b_834_ = v___y_836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_848_, lean_object* v_i_849_, lean_object* v_stop_850_, lean_object* v_b_851_){
_start:
{
size_t v_i_boxed_852_; size_t v_stop_boxed_853_; lean_object* v_res_854_; 
v_i_boxed_852_ = lean_unbox_usize(v_i_849_);
lean_dec(v_i_849_);
v_stop_boxed_853_ = lean_unbox_usize(v_stop_850_);
lean_dec(v_stop_850_);
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_848_, v_i_boxed_852_, v_stop_boxed_853_, v_b_851_);
lean_dec_ref(v_as_848_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_855_, lean_object* v_as_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_array_get_size(v_as_856_);
v___x_859_ = lean_nat_dec_lt(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
return v_initState_855_;
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_858_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_856_, v___x_860_, v___x_861_, v_initState_855_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_863_, lean_object* v_as_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_863_, v_as_864_);
lean_dec_ref(v_as_864_);
return v_res_865_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_box(0);
v___x_867_ = lean_unsigned_to_nat(16u);
v___x_868_ = lean_mk_array(v___x_867_, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; 
v___x_875_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_876_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_877_ = 1;
v___x_878_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_875_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*2, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_881_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_880_, v_es_879_);
v___x_882_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_883_);
lean_dec_ref(v_es_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_902_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias___lam__0(lean_object* v_addEntryFn_905_, lean_object* v___x_906_, lean_object* v_s_907_){
_start:
{
lean_object* v_importedEntries_908_; lean_object* v_state_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
v_importedEntries_908_ = lean_ctor_get(v_s_907_, 0);
v_state_909_ = lean_ctor_get(v_s_907_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_s_907_);
if (v_isSharedCheck_917_ == 0)
{
v___x_911_ = v_s_907_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_state_909_);
lean_inc(v_importedEntries_908_);
lean_dec(v_s_907_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_state_913_; lean_object* v___x_915_; 
v_state_913_ = lean_apply_2(v_addEntryFn_905_, v_state_909_, v___x_906_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v_state_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_importedEntries_908_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_state_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_918_, lean_object* v_a_919_, lean_object* v_e_920_){
_start:
{
lean_object* v___x_921_; lean_object* v_toEnvExtension_922_; lean_object* v_addEntryFn_923_; lean_object* v_asyncMode_924_; uint8_t v_logWrites_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_921_ = l_Lean_aliasExtension;
v_toEnvExtension_922_ = lean_ctor_get(v___x_921_, 0);
v_addEntryFn_923_ = lean_ctor_get(v___x_921_, 3);
v_asyncMode_924_ = lean_ctor_get(v_toEnvExtension_922_, 2);
v_logWrites_925_ = lean_ctor_get_uint8(v_toEnvExtension_922_, sizeof(void*)*6);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_a_919_);
lean_ctor_set(v___x_926_, 1, v_e_920_);
lean_inc(v_addEntryFn_923_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_addAlias___lam__0), 3, 2);
lean_closure_set(v___f_927_, 0, v_addEntryFn_923_);
lean_closure_set(v___f_927_, 1, v___x_926_);
v___x_928_ = lean_box(0);
v___x_929_ = 1;
if (v_logWrites_925_ == 0)
{
lean_object* v___x_930_; 
lean_inc_ref(v_toEnvExtension_922_);
v___x_930_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_922_, v_env_918_, v___f_927_, v_asyncMode_924_, v___x_928_, v___x_929_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc_ref_n(v_toEnvExtension_922_, 2);
v___x_931_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_922_, v_env_918_);
lean_dec_ref(v_env_918_);
v___x_932_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_922_, v___x_931_, v___f_927_, v_asyncMode_924_, v___x_928_, v___x_929_);
return v___x_932_;
}
}
}
static lean_object* _init_l_Lean_getAliasState___closed__0(void){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_SMap_instInhabited___redArg();
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_934_){
_start:
{
lean_object* v___x_935_; lean_object* v_toEnvExtension_936_; lean_object* v_asyncMode_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_935_ = l_Lean_aliasExtension;
v_toEnvExtension_936_ = lean_ctor_get(v___x_935_, 0);
v_asyncMode_937_ = lean_ctor_get(v_toEnvExtension_936_, 2);
v___x_938_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_939_ = lean_box(0);
v___x_940_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_938_, v___x_935_, v_env_934_, v_asyncMode_937_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_941_, uint8_t v_skipProtected_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
if (lean_obj_tag(v_a_943_) == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v_env_941_);
v___x_945_ = l_List_reverse___redArg(v_a_944_);
return v___x_945_;
}
else
{
lean_object* v_head_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_958_; 
v_head_946_ = lean_ctor_get(v_a_943_, 0);
v_tail_947_ = lean_ctor_get(v_a_943_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_958_ == 0)
{
v___x_949_ = v_a_943_;
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_inc(v_head_946_);
lean_dec(v_a_943_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
uint8_t v___x_951_; 
lean_inc(v_head_946_);
lean_inc_ref(v_env_941_);
v___x_951_ = l_Lean_isProtected(v_env_941_, v_head_946_);
if (v___x_951_ == 0)
{
if (v_skipProtected_942_ == 0)
{
lean_del_object(v___x_949_);
lean_dec(v_head_946_);
v_a_943_ = v_tail_947_;
goto _start;
}
else
{
lean_object* v___x_954_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_a_944_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_head_946_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_a_944_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_a_943_ = v_tail_947_;
v_a_944_ = v___x_954_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_949_);
lean_dec(v_head_946_);
v_a_943_ = v_tail_947_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_959_, lean_object* v_skipProtected_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
uint8_t v_skipProtected_boxed_963_; lean_object* v_res_964_; 
v_skipProtected_boxed_963_ = lean_unbox(v_skipProtected_960_);
v_res_964_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_959_, v_skipProtected_boxed_963_, v_a_961_, v_a_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_965_, lean_object* v_a_966_, uint8_t v_skipProtected_967_){
_start:
{
lean_object* v___x_968_; lean_object* v_toEnvExtension_969_; lean_object* v_asyncMode_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_968_ = l_Lean_aliasExtension;
v_toEnvExtension_969_ = lean_ctor_get(v___x_968_, 0);
v_asyncMode_970_ = lean_ctor_get(v_toEnvExtension_969_, 2);
v___x_971_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_972_ = lean_box(0);
lean_inc_ref(v_env_965_);
v___x_973_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_971_, v___x_968_, v_env_965_, v_asyncMode_970_, v___x_972_);
v___x_974_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_973_, v_a_966_);
lean_dec(v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v_env_965_);
v___x_975_ = lean_box(0);
return v___x_975_;
}
else
{
if (v_skipProtected_967_ == 0)
{
lean_object* v_val_976_; 
lean_dec_ref(v_env_965_);
v_val_976_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v___x_974_, 1);
return v_val_976_;
}
else
{
lean_object* v_val_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_val_977_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v___x_974_, 1);
v___x_978_ = lean_box(0);
v___x_979_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_965_, v_skipProtected_967_, v_val_977_, v___x_978_);
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_980_, lean_object* v_a_981_, lean_object* v_skipProtected_982_){
_start:
{
uint8_t v_skipProtected_boxed_983_; lean_object* v_res_984_; 
v_skipProtected_boxed_983_ = lean_unbox(v_skipProtected_982_);
v_res_984_ = l_Lean_getAliases(v_env_980_, v_a_981_, v_skipProtected_boxed_983_);
lean_dec(v_a_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_985_, lean_object* v_as_986_, lean_object* v_a_987_, lean_object* v_es_988_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_985_, v_es_988_);
if (v___x_989_ == 0)
{
lean_dec(v_a_987_);
return v_as_986_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_990_, 0, v_a_987_);
lean_ctor_set(v___x_990_, 1, v_as_986_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_991_, lean_object* v_as_992_, lean_object* v_a_993_, lean_object* v_es_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_getRevAliases___lam__0(v_e_991_, v_as_992_, v_a_993_, v_es_994_);
lean_dec(v_es_994_);
lean_dec(v_e_991_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_i_999_, lean_object* v_acc_1000_){
_start:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_get_size(v_keys_997_);
v___x_1002_ = lean_nat_dec_lt(v_i_999_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec(v_i_999_);
lean_dec(v_f_996_);
return v_acc_1000_;
}
else
{
lean_object* v_k_1003_; lean_object* v_v_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_k_1003_ = lean_array_fget_borrowed(v_keys_997_, v_i_999_);
v_v_1004_ = lean_array_fget_borrowed(v_vals_998_, v_i_999_);
lean_inc(v_f_996_);
lean_inc(v_v_1004_);
lean_inc(v_k_1003_);
v___x_1005_ = lean_apply_3(v_f_996_, v_acc_1000_, v_k_1003_, v_v_1004_);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_nat_add(v_i_999_, v___x_1006_);
lean_dec(v_i_999_);
v_i_999_ = v___x_1007_;
v_acc_1000_ = v___x_1005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_1009_, lean_object* v_keys_1010_, lean_object* v_vals_1011_, lean_object* v_i_1012_, lean_object* v_acc_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1009_, v_keys_1010_, v_vals_1011_, v_i_1012_, v_acc_1013_);
lean_dec_ref(v_vals_1011_);
lean_dec_ref(v_keys_1010_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1015_, lean_object* v_as_1016_, size_t v_i_1017_, size_t v_stop_1018_, lean_object* v_b_1019_){
_start:
{
lean_object* v___y_1021_; uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_eq(v_i_1017_, v_stop_1018_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_array_uget_borrowed(v_as_1016_, v_i_1017_);
switch(lean_obj_tag(v___x_1026_))
{
case 0:
{
lean_object* v_key_1027_; lean_object* v_val_1028_; lean_object* v___x_1029_; 
v_key_1027_ = lean_ctor_get(v___x_1026_, 0);
v_val_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_f_1015_);
lean_inc(v_val_1028_);
lean_inc(v_key_1027_);
v___x_1029_ = lean_apply_3(v_f_1015_, v_b_1019_, v_key_1027_, v_val_1028_);
v___y_1021_ = v___x_1029_;
goto v___jp_1020_;
}
case 1:
{
lean_object* v_node_1030_; lean_object* v___x_1031_; 
v_node_1030_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_f_1015_);
v___x_1031_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1015_, v_node_1030_, v_b_1019_);
v___y_1021_ = v___x_1031_;
goto v___jp_1020_;
}
default: 
{
v___y_1021_ = v_b_1019_;
goto v___jp_1020_;
}
}
}
else
{
lean_dec(v_f_1015_);
return v_b_1019_;
}
v___jp_1020_:
{
size_t v___x_1022_; size_t v___x_1023_; 
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1017_, v___x_1022_);
v_i_1017_ = v___x_1023_;
v_b_1019_ = v___y_1021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1033_) == 0)
{
lean_object* v_es_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_es_1035_ = lean_ctor_get(v_x_1033_, 0);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_array_get_size(v_es_1035_);
v___x_1038_ = lean_nat_dec_lt(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec(v_f_1032_);
return v_x_1034_;
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1037_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1032_, v_es_1035_, v___x_1039_, v___x_1040_, v_x_1034_);
return v___x_1041_;
}
}
else
{
lean_object* v_ks_1042_; lean_object* v_vs_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_ks_1042_ = lean_ctor_get(v_x_1033_, 0);
v_vs_1043_ = lean_ctor_get(v_x_1033_, 1);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1032_, v_ks_1042_, v_vs_1043_, v___x_1044_, v_x_1034_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1046_, v_x_1047_, v_x_1048_);
lean_dec_ref(v_x_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_1050_, lean_object* v_as_1051_, lean_object* v_i_1052_, lean_object* v_stop_1053_, lean_object* v_b_1054_){
_start:
{
size_t v_i_boxed_1055_; size_t v_stop_boxed_1056_; lean_object* v_res_1057_; 
v_i_boxed_1055_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_stop_boxed_1056_ = lean_unbox_usize(v_stop_1053_);
lean_dec(v_stop_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1050_, v_as_1051_, v_i_boxed_1055_, v_stop_boxed_1056_, v_b_1054_);
lean_dec_ref(v_as_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1058_, lean_object* v_x1_1059_, lean_object* v_x2_1060_, lean_object* v_x3_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_apply_3(v_f_1058_, v_x1_1059_, v_x2_1060_, v_x3_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1063_, lean_object* v_f_1064_, lean_object* v_init_1065_){
_start:
{
lean_object* v___f_1066_; lean_object* v___x_1067_; 
v___f_1066_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1066_, 0, v_f_1064_);
v___x_1067_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1066_, v_map_1063_, v_init_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1068_, lean_object* v_f_1069_, lean_object* v_init_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1068_, v_f_1069_, v_init_1070_);
lean_dec_ref(v_map_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_dec(v_f_1072_);
return v_x_1073_;
}
else
{
lean_object* v_key_1075_; lean_object* v_value_1076_; lean_object* v_tail_1077_; lean_object* v___x_1078_; 
v_key_1075_ = lean_ctor_get(v_x_1074_, 0);
lean_inc(v_key_1075_);
v_value_1076_ = lean_ctor_get(v_x_1074_, 1);
lean_inc(v_value_1076_);
v_tail_1077_ = lean_ctor_get(v_x_1074_, 2);
lean_inc(v_tail_1077_);
lean_dec_ref_known(v_x_1074_, 3);
lean_inc(v_f_1072_);
v___x_1078_ = lean_apply_3(v_f_1072_, v_x_1073_, v_key_1075_, v_value_1076_);
v_x_1073_ = v___x_1078_;
v_x_1074_ = v_tail_1077_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1080_, lean_object* v_as_1081_, size_t v_i_1082_, size_t v_stop_1083_, lean_object* v_b_1084_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_eq(v_i_1082_, v_stop_1083_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; 
v___x_1086_ = lean_array_uget_borrowed(v_as_1081_, v_i_1082_);
lean_inc(v___x_1086_);
lean_inc(v_f_1080_);
v___x_1087_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1080_, v_b_1084_, v___x_1086_);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1082_, v___x_1088_);
v_i_1082_ = v___x_1089_;
v_b_1084_ = v___x_1087_;
goto _start;
}
else
{
lean_dec(v_f_1080_);
return v_b_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1091_, lean_object* v_as_1092_, lean_object* v_i_1093_, lean_object* v_stop_1094_, lean_object* v_b_1095_){
_start:
{
size_t v_i_boxed_1096_; size_t v_stop_boxed_1097_; lean_object* v_res_1098_; 
v_i_boxed_1096_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_stop_boxed_1097_ = lean_unbox_usize(v_stop_1094_);
lean_dec(v_stop_1094_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1091_, v_as_1092_, v_i_boxed_1096_, v_stop_boxed_1097_, v_b_1095_);
lean_dec_ref(v_as_1092_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1099_, lean_object* v_init_1100_, lean_object* v_m_1101_){
_start:
{
lean_object* v_map_u2081_1102_; lean_object* v_map_u2082_1103_; lean_object* v_buckets_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_map_u2081_1102_ = lean_ctor_get(v_m_1101_, 0);
v_map_u2082_1103_ = lean_ctor_get(v_m_1101_, 1);
v_buckets_1104_ = lean_ctor_get(v_map_u2081_1102_, 1);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_array_get_size(v_buckets_1104_);
v___x_1107_ = lean_nat_dec_lt(v___x_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1103_, v_f_1099_, v_init_1100_);
return v___x_1108_;
}
else
{
size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = lean_usize_of_nat(v___x_1106_);
lean_inc(v_f_1099_);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1099_, v_buckets_1104_, v___x_1109_, v___x_1110_, v_init_1100_);
v___x_1112_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1103_, v_f_1099_, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1113_, lean_object* v_init_1114_, lean_object* v_m_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1113_, v_init_1114_, v_m_1115_);
lean_dec_ref(v_m_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1117_, lean_object* v_e_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v_toEnvExtension_1120_; lean_object* v_asyncMode_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1119_ = l_Lean_aliasExtension;
v_toEnvExtension_1120_ = lean_ctor_get(v___x_1119_, 0);
v_asyncMode_1121_ = lean_ctor_get(v_toEnvExtension_1120_, 2);
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1122_, 0, v_e_1118_);
v___x_1123_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_box(0);
v___x_1126_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1123_, v___x_1119_, v_env_1117_, v_asyncMode_1121_, v___x_1125_);
v___x_1127_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1122_, v___x_1124_, v___x_1126_);
lean_dec(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_00_u03c3_1129_, lean_object* v_f_1130_, lean_object* v_init_1131_, lean_object* v_m_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1130_, v_init_1131_, v_m_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1134_, lean_object* v_00_u03c3_1135_, lean_object* v_f_1136_, lean_object* v_init_1137_, lean_object* v_m_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1134_, v_00_u03c3_1135_, v_f_1136_, v_init_1137_, v_m_1138_);
lean_dec_ref(v_m_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1140_, lean_object* v_00_u03c3_1141_, lean_object* v_f_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1142_, v_x_1143_, v_x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1146_, lean_object* v_00_u03b2_1147_, lean_object* v_map_1148_, lean_object* v_f_1149_, lean_object* v_init_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1148_, v_f_1149_, v_init_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_map_1154_, lean_object* v_f_1155_, lean_object* v_init_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1152_, v_00_u03b2_1153_, v_map_1154_, v_f_1155_, v_init_1156_);
lean_dec_ref(v_map_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1158_, lean_object* v_00_u03c3_1159_, lean_object* v_f_1160_, lean_object* v_as_1161_, size_t v_i_1162_, size_t v_stop_1163_, lean_object* v_b_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1160_, v_as_1161_, v_i_1162_, v_stop_1163_, v_b_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1166_, lean_object* v_00_u03c3_1167_, lean_object* v_f_1168_, lean_object* v_as_1169_, lean_object* v_i_1170_, lean_object* v_stop_1171_, lean_object* v_b_1172_){
_start:
{
size_t v_i_boxed_1173_; size_t v_stop_boxed_1174_; lean_object* v_res_1175_; 
v_i_boxed_1173_ = lean_unbox_usize(v_i_1170_);
lean_dec(v_i_1170_);
v_stop_boxed_1174_ = lean_unbox_usize(v_stop_1171_);
lean_dec(v_stop_1171_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1166_, v_00_u03c3_1167_, v_f_1168_, v_as_1169_, v_i_boxed_1173_, v_stop_boxed_1174_, v_b_1172_);
lean_dec_ref(v_as_1169_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1176_, lean_object* v_f_1177_, lean_object* v_init_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1177_, v_map_1176_, v_init_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1180_, lean_object* v_f_1181_, lean_object* v_init_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1180_, v_f_1181_, v_init_1182_);
lean_dec_ref(v_map_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_map_1186_, lean_object* v_f_1187_, lean_object* v_init_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1187_, v_map_1186_, v_init_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_map_1192_, lean_object* v_f_1193_, lean_object* v_init_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1190_, v_00_u03b2_1191_, v_map_1192_, v_f_1193_, v_init_1194_);
lean_dec_ref(v_map_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1196_, lean_object* v_00_u03b1_1197_, lean_object* v_00_u03b2_1198_, lean_object* v_f_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1199_, v_x_1200_, v_x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1203_, lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_f_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1203_, v_00_u03b1_1204_, v_00_u03b2_1205_, v_f_1206_, v_x_1207_, v_x_1208_);
lean_dec_ref(v_x_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_00_u03c3_1212_, lean_object* v_f_1213_, lean_object* v_as_1214_, size_t v_i_1215_, size_t v_stop_1216_, lean_object* v_b_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1213_, v_as_1214_, v_i_1215_, v_stop_1216_, v_b_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_00_u03c3_1221_, lean_object* v_f_1222_, lean_object* v_as_1223_, lean_object* v_i_1224_, lean_object* v_stop_1225_, lean_object* v_b_1226_){
_start:
{
size_t v_i_boxed_1227_; size_t v_stop_boxed_1228_; lean_object* v_res_1229_; 
v_i_boxed_1227_ = lean_unbox_usize(v_i_1224_);
lean_dec(v_i_1224_);
v_stop_boxed_1228_ = lean_unbox_usize(v_stop_1225_);
lean_dec(v_stop_1225_);
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1219_, v_00_u03b2_1220_, v_00_u03c3_1221_, v_f_1222_, v_as_1223_, v_i_boxed_1227_, v_stop_boxed_1228_, v_b_1226_);
lean_dec_ref(v_as_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1230_, lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_f_1233_, lean_object* v_keys_1234_, lean_object* v_vals_1235_, lean_object* v_heq_1236_, lean_object* v_i_1237_, lean_object* v_acc_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1233_, v_keys_1234_, v_vals_1235_, v_i_1237_, v_acc_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1240_, lean_object* v_00_u03b1_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_f_1243_, lean_object* v_keys_1244_, lean_object* v_vals_1245_, lean_object* v_heq_1246_, lean_object* v_i_1247_, lean_object* v_acc_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1240_, v_00_u03b1_1241_, v_00_u03b2_1242_, v_f_1243_, v_keys_1244_, v_vals_1245_, v_heq_1246_, v_i_1247_, v_acc_1248_);
lean_dec_ref(v_vals_1245_);
lean_dec_ref(v_keys_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1250_, lean_object* v_declName_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_Environment_containsOnBranch(v_env_1250_, v_declName_1251_);
if (v___x_1252_ == 0)
{
uint8_t v___x_1253_; 
lean_inc(v_declName_1251_);
lean_inc_ref(v_env_1250_);
v___x_1253_ = lean_is_reserved_name(v_env_1250_, v_declName_1251_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = 1;
v___x_1255_ = l_Lean_Environment_contains(v_env_1250_, v_declName_1251_, v___x_1254_);
return v___x_1255_;
}
else
{
lean_dec(v_declName_1251_);
lean_dec_ref(v_env_1250_);
return v___x_1253_;
}
}
else
{
lean_dec(v_declName_1251_);
lean_dec_ref(v_env_1250_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1256_, lean_object* v_declName_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1256_, v_declName_1257_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1260_, lean_object* v_decl_1261_, lean_object* v_ref_1262_){
_start:
{
lean_object* v_defValue_1264_; lean_object* v_descr_1265_; lean_object* v_deprecation_x3f_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_defValue_1264_ = lean_ctor_get(v_decl_1261_, 0);
v_descr_1265_ = lean_ctor_get(v_decl_1261_, 1);
v_deprecation_x3f_1266_ = lean_ctor_get(v_decl_1261_, 2);
v___x_1267_ = lean_alloc_ctor(1, 0, 1);
v___x_1268_ = lean_unbox(v_defValue_1264_);
lean_ctor_set_uint8(v___x_1267_, 0, v___x_1268_);
lean_inc(v_deprecation_x3f_1266_);
lean_inc_ref(v_descr_1265_);
lean_inc_n(v_name_1260_, 2);
v___x_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1269_, 0, v_name_1260_);
lean_ctor_set(v___x_1269_, 1, v_ref_1262_);
lean_ctor_set(v___x_1269_, 2, v___x_1267_);
lean_ctor_set(v___x_1269_, 3, v_descr_1265_);
lean_ctor_set(v___x_1269_, 4, v_deprecation_x3f_1266_);
v___x_1270_ = lean_register_option(v_name_1260_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1279_);
v___x_1272_ = v___x_1270_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v___x_1270_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_inc(v_defValue_1264_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_name_1260_);
lean_ctor_set(v___x_1274_, 1, v_defValue_1264_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_name_1260_);
v_a_1280_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1270_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1270_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1288_, lean_object* v_decl_1289_, lean_object* v_ref_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1288_, v_decl_1289_, v_ref_1290_);
lean_dec_ref(v_decl_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1311_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1312_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1313_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1310_, v___x_1311_, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1335_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1336_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1337_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1334_, v___x_1335_, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1340_, lean_object* v_opt_1341_){
_start:
{
lean_object* v_name_1342_; lean_object* v_defValue_1343_; lean_object* v_map_1344_; lean_object* v___x_1345_; 
v_name_1342_ = lean_ctor_get(v_opt_1341_, 0);
v_defValue_1343_ = lean_ctor_get(v_opt_1341_, 1);
v_map_1344_ = lean_ctor_get(v_opts_1340_, 0);
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1344_, v_name_1342_);
if (lean_obj_tag(v___x_1345_) == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_unbox(v_defValue_1343_);
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; 
v_val_1347_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1347_);
lean_dec_ref_known(v___x_1345_, 1);
if (lean_obj_tag(v_val_1347_) == 1)
{
uint8_t v_v_1348_; 
v_v_1348_ = lean_ctor_get_uint8(v_val_1347_, 0);
lean_dec_ref_known(v_val_1347_, 0);
return v_v_1348_;
}
else
{
uint8_t v___x_1349_; 
lean_dec(v_val_1347_);
v___x_1349_ = lean_unbox(v_defValue_1343_);
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1350_, lean_object* v_opt_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1350_, v_opt_1351_);
lean_dec_ref(v_opt_1351_);
lean_dec_ref(v_opts_1350_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1357_, lean_object* v_env_1358_, lean_object* v_as_1359_, size_t v_sz_1360_, size_t v_i_1361_, lean_object* v_b_1362_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1361_, v_sz_1360_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v_env_1358_);
lean_dec(v_declName_1357_);
lean_inc_ref(v_b_1362_);
return v_b_1362_;
}
else
{
lean_object* v_a_1364_; lean_object* v_toImport_1365_; lean_object* v_module_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_a_1364_ = lean_array_uget_borrowed(v_as_1359_, v_i_1361_);
v_toImport_1365_ = lean_ctor_get(v_a_1364_, 0);
v_module_1366_ = lean_ctor_get(v_toImport_1365_, 0);
v___x_1367_ = lean_box(0);
lean_inc(v_declName_1357_);
lean_inc(v_module_1366_);
v___x_1368_ = l_Lean_mkPrivateNameCore(v_module_1366_, v_declName_1357_);
lean_inc(v___x_1368_);
lean_inc_ref(v_env_1358_);
v___x_1369_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1358_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; 
lean_dec(v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_add(v_i_1361_, v___x_1371_);
v_i_1361_ = v___x_1372_;
v_b_1362_ = v___x_1370_;
goto _start;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_env_1358_);
lean_dec(v_declName_1357_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1368_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___x_1367_);
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1377_, lean_object* v_env_1378_, lean_object* v_as_1379_, lean_object* v_sz_1380_, lean_object* v_i_1381_, lean_object* v_b_1382_){
_start:
{
size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1380_);
lean_dec(v_sz_1380_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1377_, v_env_1378_, v_as_1379_, v_sz_boxed_1383_, v_i_boxed_1384_, v_b_1382_);
lean_dec_ref(v_b_1382_);
lean_dec_ref(v_as_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1386_, lean_object* v_opts_1387_, lean_object* v_declName_1388_){
_start:
{
uint8_t v_isExporting_1404_; 
v_isExporting_1404_ = lean_ctor_get_uint8(v_env_1386_, sizeof(void*)*13);
if (v_isExporting_1404_ == 0)
{
goto v___jp_1389_;
}
else
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1406_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1387_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_declName_1388_);
lean_dec_ref(v_env_1386_);
v___x_1407_ = lean_box(0);
return v___x_1407_;
}
else
{
goto v___jp_1389_;
}
}
v___jp_1389_:
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
lean_inc(v_declName_1388_);
v___x_1390_ = l_Lean_mkPrivateName(v_env_1386_, v_declName_1388_);
lean_inc(v___x_1390_);
lean_inc_ref(v_env_1386_);
v___x_1391_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1386_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; uint8_t v_isModule_1393_; 
lean_dec(v___x_1390_);
v___x_1392_ = l_Lean_Environment_header(v_env_1386_);
v_isModule_1393_ = lean_ctor_get_uint8(v___x_1392_, sizeof(void*)*8 + 4);
if (v_isModule_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec_ref(v___x_1392_);
lean_dec(v_declName_1388_);
lean_dec_ref(v_env_1386_);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
lean_object* v_importAllModules_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; size_t v_sz_1398_; size_t v___x_1399_; lean_object* v___x_1400_; lean_object* v_fst_1401_; 
v_importAllModules_1395_ = lean_ctor_get(v___x_1392_, 6);
lean_inc_ref(v_importAllModules_1395_);
lean_dec_ref(v___x_1392_);
v___x_1396_ = lean_box(0);
v___x_1397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1398_ = lean_array_size(v_importAllModules_1395_);
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1388_, v_env_1386_, v_importAllModules_1395_, v_sz_1398_, v___x_1399_, v___x_1397_);
lean_dec_ref(v_importAllModules_1395_);
v_fst_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_fst_1401_);
lean_dec_ref(v___x_1400_);
if (lean_obj_tag(v_fst_1401_) == 0)
{
return v___x_1396_;
}
else
{
lean_object* v_val_1402_; 
v_val_1402_ = lean_ctor_get(v_fst_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_fst_1401_, 1);
return v_val_1402_;
}
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_declName_1388_);
lean_dec_ref(v_env_1386_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1390_);
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1408_, lean_object* v_opts_1409_, lean_object* v_declName_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1408_, v_opts_1409_, v_declName_1410_);
lean_dec_ref(v_opts_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1412_, lean_object* v_opts_1413_, lean_object* v_ns_1414_, lean_object* v_id_1415_){
_start:
{
lean_object* v_resolvedId_1416_; uint8_t v___x_1417_; lean_object* v_resolvedIds_1418_; 
lean_inc(v_id_1415_);
v_resolvedId_1416_ = l_Lean_Name_append(v_ns_1414_, v_id_1415_);
v___x_1417_ = l_Lean_Name_isAtomic(v_id_1415_);
lean_dec(v_id_1415_);
lean_inc_ref(v_env_1412_);
v_resolvedIds_1418_ = l_Lean_getAliases(v_env_1412_, v_resolvedId_1416_, v___x_1417_);
if (v___x_1417_ == 0)
{
goto v___jp_1419_;
}
else
{
uint8_t v___x_1425_; 
lean_inc(v_resolvedId_1416_);
lean_inc_ref(v_env_1412_);
v___x_1425_ = l_Lean_isProtected(v_env_1412_, v_resolvedId_1416_);
if (v___x_1425_ == 0)
{
goto v___jp_1419_;
}
else
{
lean_dec(v_resolvedId_1416_);
lean_dec_ref(v_env_1412_);
return v_resolvedIds_1418_;
}
}
v___jp_1419_:
{
uint8_t v___x_1420_; 
lean_inc(v_resolvedId_1416_);
lean_inc_ref(v_env_1412_);
v___x_1420_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1412_, v_resolvedId_1416_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1412_, v_opts_1413_, v_resolvedId_1416_);
if (lean_obj_tag(v___x_1421_) == 1)
{
lean_object* v_val_1422_; lean_object* v___x_1423_; 
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_val_1422_);
lean_ctor_set(v___x_1423_, 1, v_resolvedIds_1418_);
return v___x_1423_;
}
else
{
lean_dec(v___x_1421_);
return v_resolvedIds_1418_;
}
}
else
{
lean_object* v___x_1424_; 
lean_dec_ref(v_env_1412_);
v___x_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_resolvedId_1416_);
lean_ctor_set(v___x_1424_, 1, v_resolvedIds_1418_);
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1426_, lean_object* v_opts_1427_, lean_object* v_ns_1428_, lean_object* v_id_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1426_, v_opts_1427_, v_ns_1428_, v_id_1429_);
lean_dec_ref(v_opts_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1431_, lean_object* v_opts_1432_, lean_object* v_id_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 1)
{
lean_object* v_pre_1435_; lean_object* v___x_1436_; 
v_pre_1435_ = lean_ctor_get(v_x_1434_, 0);
lean_inc(v_pre_1435_);
lean_inc(v_id_1433_);
lean_inc_ref(v_env_1431_);
v___x_1436_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1431_, v_opts_1432_, v_x_1434_, v_id_1433_);
if (lean_obj_tag(v___x_1436_) == 0)
{
v_x_1434_ = v_pre_1435_;
goto _start;
}
else
{
lean_dec(v_pre_1435_);
lean_dec(v_id_1433_);
lean_dec_ref(v_env_1431_);
return v___x_1436_;
}
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_x_1434_);
lean_dec(v_id_1433_);
lean_dec_ref(v_env_1431_);
v___x_1438_ = lean_box(0);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1439_, lean_object* v_opts_1440_, lean_object* v_id_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1439_, v_opts_1440_, v_id_1441_, v_x_1442_);
lean_dec_ref(v_opts_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1444_, lean_object* v_opts_1445_, lean_object* v_id_1446_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = l_Lean_Name_isAtomic(v_id_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_resolvedId_1450_; uint8_t v___x_1451_; 
v___x_1448_ = l_Lean_rootNamespace;
v___x_1449_ = lean_box(0);
v_resolvedId_1450_ = l_Lean_Name_replacePrefix(v_id_1446_, v___x_1448_, v___x_1449_);
lean_inc(v_resolvedId_1450_);
lean_inc_ref(v_env_1444_);
v___x_1451_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1444_, v_resolvedId_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1444_, v_opts_1445_, v_resolvedId_1450_);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; 
lean_dec_ref(v_env_1444_);
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_resolvedId_1450_);
return v___x_1453_;
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_id_1446_);
lean_dec_ref(v_env_1444_);
v___x_1454_ = lean_box(0);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1455_, lean_object* v_opts_1456_, lean_object* v_id_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1455_, v_opts_1456_, v_id_1457_);
lean_dec_ref(v_opts_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1459_, lean_object* v_opts_1460_, lean_object* v_id_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_dec(v_id_1461_);
lean_dec_ref(v_env_1459_);
return v_x_1463_;
}
else
{
lean_object* v_head_1464_; 
v_head_1464_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_head_1464_);
if (lean_obj_tag(v_head_1464_) == 0)
{
lean_object* v_tail_1465_; lean_object* v_ns_1466_; lean_object* v_except_1467_; uint8_t v___x_1468_; 
v_tail_1465_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_tail_1465_);
lean_dec_ref_known(v_x_1462_, 2);
v_ns_1466_ = lean_ctor_get(v_head_1464_, 0);
lean_inc(v_ns_1466_);
v_except_1467_ = lean_ctor_get(v_head_1464_, 1);
lean_inc(v_except_1467_);
lean_dec_ref_known(v_head_1464_, 2);
v___x_1468_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1461_, v_except_1467_);
lean_dec(v_except_1467_);
if (v___x_1468_ == 0)
{
lean_object* v_newResolvedIds_1469_; lean_object* v___x_1470_; 
lean_inc(v_id_1461_);
lean_inc_ref(v_env_1459_);
v_newResolvedIds_1469_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1459_, v_opts_1460_, v_ns_1466_, v_id_1461_);
v___x_1470_ = l_List_appendTR___redArg(v_newResolvedIds_1469_, v_x_1463_);
v_x_1462_ = v_tail_1465_;
v_x_1463_ = v___x_1470_;
goto _start;
}
else
{
lean_dec(v_ns_1466_);
v_x_1462_ = v_tail_1465_;
goto _start;
}
}
else
{
lean_object* v_tail_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1493_; 
v_tail_1473_ = lean_ctor_get(v_x_1462_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_x_1462_, 0);
lean_dec(v_unused_1494_);
v___x_1475_ = v_x_1462_;
v_isShared_1476_ = v_isSharedCheck_1493_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_tail_1473_);
lean_dec(v_x_1462_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1493_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_id_1477_; lean_object* v_declName_1478_; uint8_t v___x_1479_; 
v_id_1477_ = lean_ctor_get(v_head_1464_, 0);
lean_inc(v_id_1477_);
v_declName_1478_ = lean_ctor_get(v_head_1464_, 1);
lean_inc(v_declName_1478_);
lean_dec_ref_known(v_head_1464_, 2);
v___x_1479_ = lean_name_eq(v_id_1477_, v_id_1461_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Lean_Name_isPrefixOf(v_id_1477_, v_id_1461_);
if (v___x_1480_ == 0)
{
lean_dec(v_declName_1478_);
lean_dec(v_id_1477_);
lean_del_object(v___x_1475_);
v_x_1462_ = v_tail_1473_;
goto _start;
}
else
{
lean_object* v_candidate_1482_; uint8_t v___x_1483_; 
lean_inc(v_id_1461_);
v_candidate_1482_ = l_Lean_Name_replacePrefix(v_id_1461_, v_id_1477_, v_declName_1478_);
lean_dec(v_declName_1478_);
lean_dec(v_id_1477_);
lean_inc(v_candidate_1482_);
lean_inc_ref(v_env_1459_);
v___x_1483_ = l_Lean_Environment_contains(v_env_1459_, v_candidate_1482_, v___x_1480_);
if (v___x_1483_ == 0)
{
lean_dec(v_candidate_1482_);
lean_del_object(v___x_1475_);
v_x_1462_ = v_tail_1473_;
goto _start;
}
else
{
lean_object* v___x_1486_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_x_1463_);
lean_ctor_set(v___x_1475_, 0, v_candidate_1482_);
v___x_1486_ = v___x_1475_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_candidate_1482_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_x_1463_);
v___x_1486_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v_x_1462_ = v_tail_1473_;
v_x_1463_ = v___x_1486_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1490_; 
lean_dec(v_id_1477_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_x_1463_);
lean_ctor_set(v___x_1475_, 0, v_declName_1478_);
v___x_1490_ = v___x_1475_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_declName_1478_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_x_1463_);
v___x_1490_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
v_x_1462_ = v_tail_1473_;
v_x_1463_ = v___x_1490_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1495_, lean_object* v_opts_1496_, lean_object* v_id_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1495_, v_opts_1496_, v_id_1497_, v_x_1498_, v_x_1499_);
lean_dec_ref(v_opts_1496_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1502_){
_start:
{
lean_object* v___f_1503_; lean_object* v___x_1504_; 
v___f_1503_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1504_ = l_List_eraseDupsBy___redArg(v___f_1503_, v_as_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
if (lean_obj_tag(v_a_1506_) == 0)
{
lean_object* v___x_1508_; 
lean_dec(v_projs_1505_);
v___x_1508_ = l_List_reverse___redArg(v_a_1507_);
return v___x_1508_;
}
else
{
lean_object* v_head_1509_; lean_object* v_tail_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1519_; 
v_head_1509_ = lean_ctor_get(v_a_1506_, 0);
v_tail_1510_ = lean_ctor_get(v_a_1506_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1512_ = v_a_1506_;
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_tail_1510_);
lean_inc(v_head_1509_);
lean_dec(v_a_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_inc(v_projs_1505_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_head_1509_);
lean_ctor_set(v___x_1514_, 1, v_projs_1505_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 1, v_a_1507_);
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_a_1507_);
v___x_1516_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v_a_1506_ = v_tail_1510_;
v_a_1507_ = v___x_1516_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1520_, lean_object* v_opts_1521_, lean_object* v_ns_1522_, lean_object* v_openDecls_1523_, lean_object* v_extractionResult_1524_, lean_object* v_id_1525_, lean_object* v_projs_1526_){
_start:
{
if (lean_obj_tag(v_id_1525_) == 1)
{
lean_object* v_pre_1527_; lean_object* v_str_1528_; lean_object* v_imported_1529_; lean_object* v_ctx_1530_; lean_object* v_scopes_1531_; lean_object* v___x_1532_; lean_object* v_id_1533_; lean_object* v___y_1535_; lean_object* v___x_1545_; lean_object* v___y_1547_; 
v_pre_1527_ = lean_ctor_get(v_id_1525_, 0);
lean_inc(v_pre_1527_);
v_str_1528_ = lean_ctor_get(v_id_1525_, 1);
lean_inc_ref(v_str_1528_);
v_imported_1529_ = lean_ctor_get(v_extractionResult_1524_, 1);
v_ctx_1530_ = lean_ctor_get(v_extractionResult_1524_, 2);
v_scopes_1531_ = lean_ctor_get(v_extractionResult_1524_, 3);
lean_inc(v_scopes_1531_);
lean_inc(v_ctx_1530_);
lean_inc(v_imported_1529_);
v___x_1532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1532_, 0, v_id_1525_);
lean_ctor_set(v___x_1532_, 1, v_imported_1529_);
lean_ctor_set(v___x_1532_, 2, v_ctx_1530_);
lean_ctor_set(v___x_1532_, 3, v_scopes_1531_);
v_id_1533_ = l_Lean_MacroScopesView_review(v___x_1532_);
lean_inc(v_ns_1522_);
lean_inc(v_id_1533_);
lean_inc_ref(v_env_1520_);
v___x_1545_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1520_, v_opts_1521_, v_id_1533_, v_ns_1522_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_id_1533_);
lean_inc_ref(v_env_1520_);
v___x_1552_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1520_, v_opts_1521_, v_id_1533_);
if (lean_obj_tag(v___x_1552_) == 0)
{
uint8_t v___x_1553_; 
lean_inc(v_id_1533_);
lean_inc_ref(v_env_1520_);
v___x_1553_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1520_, v_id_1533_);
if (v___x_1553_ == 0)
{
v___y_1547_ = v___x_1545_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1554_; 
lean_inc(v_id_1533_);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_id_1533_);
lean_ctor_set(v___x_1554_, 1, v___x_1545_);
v___y_1547_ = v___x_1554_;
goto v___jp_1546_;
}
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v_id_1533_);
lean_dec_ref(v_str_1528_);
lean_dec(v_pre_1527_);
lean_dec(v_openDecls_1523_);
lean_dec(v_ns_1522_);
lean_dec_ref(v_env_1520_);
v_val_1555_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_val_1555_);
lean_ctor_set(v___x_1556_, 1, v_projs_1526_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
return v___x_1558_;
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_id_1533_);
lean_dec_ref(v_str_1528_);
lean_dec(v_pre_1527_);
lean_dec(v_openDecls_1523_);
lean_dec(v_ns_1522_);
lean_dec_ref(v_env_1520_);
v___x_1559_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1545_);
v___x_1560_ = lean_box(0);
v___x_1561_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1526_, v___x_1559_, v___x_1560_);
return v___x_1561_;
}
v___jp_1534_:
{
lean_object* v_resolvedIds_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v_resolvedIds_1539_; 
lean_inc(v_openDecls_1523_);
lean_inc(v_id_1533_);
lean_inc_ref_n(v_env_1520_, 2);
v_resolvedIds_1536_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1520_, v_opts_1521_, v_id_1533_, v_openDecls_1523_, v___y_1535_);
v___x_1537_ = l_Lean_Name_isAtomic(v_id_1533_);
v___x_1538_ = l_Lean_getAliases(v_env_1520_, v_id_1533_, v___x_1537_);
lean_dec(v_id_1533_);
v_resolvedIds_1539_ = l_List_appendTR___redArg(v___x_1538_, v_resolvedIds_1536_);
if (lean_obj_tag(v_resolvedIds_1539_) == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_str_1528_);
lean_ctor_set(v___x_1540_, 1, v_projs_1526_);
v_id_1525_ = v_pre_1527_;
v_projs_1526_ = v___x_1540_;
goto _start;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v_str_1528_);
lean_dec(v_pre_1527_);
lean_dec(v_openDecls_1523_);
lean_dec(v_ns_1522_);
lean_dec_ref(v_env_1520_);
v___x_1542_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1539_);
v___x_1543_ = lean_box(0);
v___x_1544_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1526_, v___x_1542_, v___x_1543_);
return v___x_1544_;
}
}
v___jp_1546_:
{
lean_object* v___x_1548_; 
lean_inc(v_id_1533_);
lean_inc_ref(v_env_1520_);
v___x_1548_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1520_, v_opts_1521_, v_id_1533_);
if (lean_obj_tag(v___x_1548_) == 1)
{
lean_object* v_val_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_val_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_val_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1545_);
v___x_1551_ = l_List_appendTR___redArg(v___x_1550_, v___y_1547_);
v___y_1535_ = v___x_1551_;
goto v___jp_1534_;
}
else
{
lean_dec(v___x_1548_);
lean_dec(v___x_1545_);
v___y_1535_ = v___y_1547_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1562_; 
lean_dec(v_projs_1526_);
lean_dec(v_id_1525_);
lean_dec(v_openDecls_1523_);
lean_dec(v_ns_1522_);
lean_dec_ref(v_env_1520_);
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1563_, lean_object* v_opts_1564_, lean_object* v_ns_1565_, lean_object* v_openDecls_1566_, lean_object* v_extractionResult_1567_, lean_object* v_id_1568_, lean_object* v_projs_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1563_, v_opts_1564_, v_ns_1565_, v_openDecls_1566_, v_extractionResult_1567_, v_id_1568_, v_projs_1569_);
lean_dec_ref(v_extractionResult_1567_);
lean_dec_ref(v_opts_1564_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1571_, lean_object* v_opts_1572_, lean_object* v_ns_1573_, lean_object* v_openDecls_1574_, lean_object* v_id_1575_){
_start:
{
lean_object* v_extractionResult_1576_; lean_object* v_name_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_extractionResult_1576_ = l_Lean_extractMacroScopes(v_id_1575_);
v_name_1577_ = lean_ctor_get(v_extractionResult_1576_, 0);
lean_inc(v_name_1577_);
v___x_1578_ = lean_box(0);
v___x_1579_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1571_, v_opts_1572_, v_ns_1573_, v_openDecls_1574_, v_extractionResult_1576_, v_name_1577_, v___x_1578_);
lean_dec_ref(v_extractionResult_1576_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1580_, lean_object* v_opts_1581_, lean_object* v_ns_1582_, lean_object* v_openDecls_1583_, lean_object* v_id_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_ResolveName_resolveGlobalName(v_env_1580_, v_opts_1581_, v_ns_1582_, v_openDecls_1583_, v_id_1584_);
lean_dec_ref(v_opts_1581_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_panic_fn_borrowed(v___x_1587_, v_msg_1586_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1592_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1593_ = lean_unsigned_to_nat(9u);
v___x_1594_ = lean_unsigned_to_nat(247u);
v___x_1595_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1596_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1597_ = l_mkPanicMessageWithDecl(v___x_1596_, v___x_1595_, v___x_1594_, v___x_1593_, v___x_1592_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1598_, lean_object* v_n_1599_, lean_object* v_ns_1600_){
_start:
{
switch(lean_obj_tag(v_ns_1600_))
{
case 1:
{
lean_object* v_pre_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_pre_1601_ = lean_ctor_get(v_ns_1600_, 0);
lean_inc(v_pre_1601_);
lean_inc(v_n_1599_);
v___x_1602_ = l_Lean_Name_append(v_ns_1600_, v_n_1599_);
lean_inc_ref(v_env_1598_);
v___x_1603_ = l_Lean_Environment_isNamespace(v_env_1598_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_dec(v___x_1602_);
v_ns_1600_ = v_pre_1601_;
goto _start;
}
else
{
lean_object* v___x_1605_; 
lean_dec(v_pre_1601_);
lean_dec(v_n_1599_);
lean_dec_ref(v_env_1598_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1602_);
return v___x_1605_;
}
}
case 0:
{
lean_object* v___x_1606_; lean_object* v_n_1607_; uint8_t v___x_1608_; 
v___x_1606_ = l_Lean_rootNamespace;
v_n_1607_ = l_Lean_Name_replacePrefix(v_n_1599_, v___x_1606_, v_ns_1600_);
v___x_1608_ = l_Lean_Environment_isNamespace(v_env_1598_, v_n_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_dec(v_n_1607_);
v___x_1609_ = lean_box(0);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_n_1607_);
return v___x_1610_;
}
}
default: 
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec(v_ns_1600_);
lean_dec(v_n_1599_);
lean_dec_ref(v_env_1598_);
v___x_1611_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1612_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1611_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1613_, lean_object* v_n_1614_, lean_object* v_x_1615_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v___x_1616_; 
lean_dec(v_n_1614_);
lean_dec_ref(v_env_1613_);
v___x_1616_ = lean_box(0);
return v___x_1616_;
}
else
{
lean_object* v_head_1617_; 
v_head_1617_ = lean_ctor_get(v_x_1615_, 0);
if (lean_obj_tag(v_head_1617_) == 0)
{
lean_object* v_tail_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1633_; 
lean_inc_ref(v_head_1617_);
v_tail_1618_ = lean_ctor_get(v_x_1615_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v_x_1615_, 0);
lean_dec(v_unused_1634_);
v___x_1620_ = v_x_1615_;
v_isShared_1621_ = v_isSharedCheck_1633_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_tail_1618_);
lean_dec(v_x_1615_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1633_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_ns_1622_; lean_object* v_except_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_ns_1622_ = lean_ctor_get(v_head_1617_, 0);
lean_inc(v_ns_1622_);
v_except_1623_ = lean_ctor_get(v_head_1617_, 1);
lean_inc(v_except_1623_);
lean_dec_ref_known(v_head_1617_, 2);
lean_inc(v_n_1614_);
v___x_1624_ = l_Lean_Name_append(v_ns_1622_, v_n_1614_);
lean_inc_ref(v_env_1613_);
v___x_1625_ = l_Lean_Environment_isNamespace(v_env_1613_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec(v___x_1624_);
lean_dec(v_except_1623_);
lean_del_object(v___x_1620_);
v_x_1615_ = v_tail_1618_;
goto _start;
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1614_, v_except_1623_);
lean_dec(v_except_1623_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1613_, v_n_1614_, v_tail_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1628_);
lean_ctor_set(v___x_1620_, 0, v___x_1624_);
v___x_1630_ = v___x_1620_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
else
{
lean_dec(v___x_1624_);
lean_del_object(v___x_1620_);
v_x_1615_ = v_tail_1618_;
goto _start;
}
}
}
}
else
{
lean_object* v_tail_1635_; 
v_tail_1635_ = lean_ctor_get(v_x_1615_, 1);
lean_inc(v_tail_1635_);
lean_dec_ref_known(v_x_1615_, 2);
v_x_1615_ = v_tail_1635_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1637_, lean_object* v_ns_1638_, lean_object* v_openDecls_1639_, lean_object* v_id_1640_){
_start:
{
lean_object* v___x_1641_; 
lean_inc(v_id_1640_);
lean_inc_ref(v_env_1637_);
v___x_1641_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1637_, v_id_1640_, v_ns_1638_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1637_, v_id_1640_, v_openDecls_1639_);
return v___x_1642_;
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_val_1643_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1644_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1637_, v_id_1640_, v_openDecls_1639_);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_val_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1646_, lean_object* v_inst_1647_){
_start:
{
lean_object* v_getCurrNamespace_1648_; lean_object* v_getOpenDecls_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1658_; 
v_getCurrNamespace_1648_ = lean_ctor_get(v_inst_1647_, 0);
v_getOpenDecls_1649_ = lean_ctor_get(v_inst_1647_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_inst_1647_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1651_ = v_inst_1647_;
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_getOpenDecls_1649_);
lean_inc(v_getCurrNamespace_1648_);
lean_dec(v_inst_1647_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
lean_inc(v_inst_1646_);
v___x_1653_ = lean_apply_2(v_inst_1646_, lean_box(0), v_getCurrNamespace_1648_);
v___x_1654_ = lean_apply_2(v_inst_1646_, lean_box(0), v_getOpenDecls_1649_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v___x_1654_);
lean_ctor_set(v___x_1651_, 0, v___x_1653_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1659_, lean_object* v_n_1660_, lean_object* v_inst_1661_, lean_object* v_inst_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1661_, v_inst_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1666_ = l_Lean_stringToMessageData(v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1669_ = l_Lean_stringToMessageData(v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1670_, lean_object* v_toPure_1671_, lean_object* v_id_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, uint8_t v_____do__lift_1677_){
_start:
{
uint8_t v_isExporting_1681_; 
v_isExporting_1681_ = lean_ctor_get_uint8(v_____do__lift_1670_, sizeof(void*)*13);
if (v_isExporting_1681_ == 0)
{
lean_dec_ref(v_inst_1676_);
lean_dec(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
lean_dec_ref(v_inst_1673_);
lean_dec(v_id_1672_);
goto v___jp_1678_;
}
else
{
uint8_t v___x_1682_; 
v___x_1682_ = l_Lean_isPrivateName(v_id_1672_);
if (v___x_1682_ == 0)
{
lean_dec_ref(v_inst_1676_);
lean_dec(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
lean_dec_ref(v_inst_1673_);
lean_dec(v_id_1672_);
goto v___jp_1678_;
}
else
{
if (v_____do__lift_1677_ == 0)
{
lean_dec_ref(v_inst_1676_);
lean_dec(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
lean_dec_ref(v_inst_1673_);
lean_dec(v_id_1672_);
goto v___jp_1678_;
}
else
{
lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec(v_toPure_1671_);
v___x_1683_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1684_ = 0;
v___x_1685_ = l_Lean_MessageData_ofConstName(v_id_1672_, v___x_1684_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1683_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_logWarning___redArg(v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v___x_1688_);
return v___x_1689_;
}
}
}
v___jp_1678_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_apply_2(v_toPure_1671_, lean_box(0), v___x_1679_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1690_, lean_object* v_toPure_1691_, lean_object* v_id_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_____do__lift_1697_){
_start:
{
uint8_t v_____do__lift_199__boxed_1698_; lean_object* v_res_1699_; 
v_____do__lift_199__boxed_1698_ = lean_unbox(v_____do__lift_1697_);
v_res_1699_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1690_, v_toPure_1691_, v_id_1692_, v_inst_1693_, v_inst_1694_, v_inst_1695_, v_inst_1696_, v_____do__lift_199__boxed_1698_);
lean_dec_ref(v_____do__lift_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1700_, lean_object* v_id_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v___x_1706_, lean_object* v_toBind_1707_, lean_object* v_____do__lift_1708_){
_start:
{
lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_inc_ref(v_inst_1705_);
lean_inc_ref(v_inst_1702_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1709_, 0, v_____do__lift_1708_);
lean_closure_set(v___f_1709_, 1, v_toPure_1700_);
lean_closure_set(v___f_1709_, 2, v_id_1701_);
lean_closure_set(v___f_1709_, 3, v_inst_1702_);
lean_closure_set(v___f_1709_, 4, v_inst_1703_);
lean_closure_set(v___f_1709_, 5, v_inst_1704_);
lean_closure_set(v___f_1709_, 6, v_inst_1705_);
v___x_1710_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1711_ = l_Lean_Option_getM___redArg(v_inst_1702_, v_inst_1705_, v___x_1706_, v___x_1710_);
v___x_1712_ = lean_apply_4(v_toBind_1707_, lean_box(0), lean_box(0), v___x_1711_, v___f_1709_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_id_1718_){
_start:
{
lean_object* v___x_1719_; lean_object* v_toApplicative_1720_; lean_object* v_toBind_1721_; lean_object* v_getEnv_1722_; lean_object* v_toPure_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; 
v___x_1719_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1720_ = lean_ctor_get(v_inst_1713_, 0);
v_toBind_1721_ = lean_ctor_get(v_inst_1713_, 1);
lean_inc_n(v_toBind_1721_, 2);
v_getEnv_1722_ = lean_ctor_get(v_inst_1714_, 0);
lean_inc(v_getEnv_1722_);
lean_dec_ref(v_inst_1714_);
v_toPure_1723_ = lean_ctor_get(v_toApplicative_1720_, 1);
lean_inc(v_toPure_1723_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1724_, 0, v_toPure_1723_);
lean_closure_set(v___f_1724_, 1, v_id_1718_);
lean_closure_set(v___f_1724_, 2, v_inst_1713_);
lean_closure_set(v___f_1724_, 3, v_inst_1716_);
lean_closure_set(v___f_1724_, 4, v_inst_1717_);
lean_closure_set(v___f_1724_, 5, v_inst_1715_);
lean_closure_set(v___f_1724_, 6, v___x_1719_);
lean_closure_set(v___f_1724_, 7, v_toBind_1721_);
v___x_1725_ = lean_apply_4(v_toBind_1721_, lean_box(0), lean_box(0), v_getEnv_1722_, v___f_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_id_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1727_, v_inst_1728_, v_inst_1729_, v_inst_1730_, v_inst_1731_, v_id_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1734_, lean_object* v_n_1735_, lean_object* v_toPure_1736_, uint8_t v___y_1737_, uint8_t v___x_1738_, lean_object* v_____r_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1734_, v_n_1735_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_box(v___y_1737_);
v___x_1742_ = lean_apply_2(v_toPure_1736_, lean_box(0), v___x_1741_);
return v___x_1742_;
}
else
{
lean_object* v_val_1743_; lean_object* v___x_1744_; uint8_t v_isModule_1745_; 
v_val_1743_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1744_ = l_Lean_Environment_header(v_env_1734_);
v_isModule_1745_ = lean_ctor_get_uint8(v___x_1744_, sizeof(void*)*8 + 4);
if (v_isModule_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v___x_1744_);
lean_dec(v_val_1743_);
v___x_1746_ = lean_box(v___x_1738_);
v___x_1747_ = lean_apply_2(v_toPure_1736_, lean_box(0), v___x_1746_);
return v___x_1747_;
}
else
{
lean_object* v_modules_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_modules_1748_ = lean_ctor_get(v___x_1744_, 3);
lean_inc_ref(v_modules_1748_);
lean_dec_ref(v___x_1744_);
v___x_1749_ = lean_array_get_size(v_modules_1748_);
v___x_1750_ = lean_nat_dec_lt(v_val_1743_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v_modules_1748_);
lean_dec(v_val_1743_);
v___x_1751_ = lean_box(v_isModule_1745_);
v___x_1752_ = lean_apply_2(v_toPure_1736_, lean_box(0), v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v_toImport_1754_; uint8_t v_importAll_1755_; 
v___x_1753_ = lean_array_fget(v_modules_1748_, v_val_1743_);
lean_dec(v_val_1743_);
lean_dec_ref(v_modules_1748_);
v_toImport_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_toImport_1754_);
lean_dec(v___x_1753_);
v_importAll_1755_ = lean_ctor_get_uint8(v_toImport_1754_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1754_);
if (v_importAll_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_box(v_isModule_1745_);
v___x_1757_ = lean_apply_2(v_toPure_1736_, lean_box(0), v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(v___y_1737_);
v___x_1759_ = lean_apply_2(v_toPure_1736_, lean_box(0), v___x_1758_);
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1760_, lean_object* v_n_1761_, lean_object* v_toPure_1762_, lean_object* v___y_1763_, lean_object* v___x_1764_, lean_object* v_____r_1765_){
_start:
{
uint8_t v___y_386__boxed_1766_; uint8_t v___x_387__boxed_1767_; lean_object* v_res_1768_; 
v___y_386__boxed_1766_ = lean_unbox(v___y_1763_);
v___x_387__boxed_1767_ = lean_unbox(v___x_1764_);
v_res_1768_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1760_, v_n_1761_, v_toPure_1762_, v___y_386__boxed_1766_, v___x_387__boxed_1767_, v_____r_1765_);
lean_dec(v_n_1761_);
lean_dec_ref(v_env_1760_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1769_, lean_object* v_n_1770_, lean_object* v_toPure_1771_, uint8_t v___x_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_toBind_1778_, uint8_t v___y_1779_, uint8_t v_____do__lift_1780_){
_start:
{
uint8_t v___y_1782_; uint8_t v_isExporting_1788_; 
v_isExporting_1788_ = lean_ctor_get_uint8(v_env_1769_, sizeof(void*)*13);
if (v_isExporting_1788_ == 0)
{
v___y_1782_ = v___y_1779_;
goto v___jp_1781_;
}
else
{
if (v_____do__lift_1780_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_toBind_1778_);
lean_dec(v_inst_1777_);
lean_dec_ref(v_inst_1776_);
lean_dec_ref(v_inst_1775_);
lean_dec_ref(v_inst_1774_);
lean_dec_ref(v_inst_1773_);
lean_dec(v_n_1770_);
lean_dec_ref(v_env_1769_);
v___x_1789_ = lean_box(v___x_1772_);
v___x_1790_ = lean_apply_2(v_toPure_1771_, lean_box(0), v___x_1789_);
return v___x_1790_;
}
else
{
v___y_1782_ = v___y_1779_;
goto v___jp_1781_;
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1783_ = lean_box(v___y_1782_);
v___x_1784_ = lean_box(v___x_1772_);
lean_inc(v_n_1770_);
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1785_, 0, v_env_1769_);
lean_closure_set(v___f_1785_, 1, v_n_1770_);
lean_closure_set(v___f_1785_, 2, v_toPure_1771_);
lean_closure_set(v___f_1785_, 3, v___x_1783_);
lean_closure_set(v___f_1785_, 4, v___x_1784_);
v___x_1786_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1773_, v_inst_1774_, v_inst_1775_, v_inst_1776_, v_inst_1777_, v_n_1770_);
v___x_1787_ = lean_apply_4(v_toBind_1778_, lean_box(0), lean_box(0), v___x_1786_, v___f_1785_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1791_, lean_object* v_n_1792_, lean_object* v_toPure_1793_, lean_object* v___x_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_toBind_1800_, lean_object* v___y_1801_, lean_object* v_____do__lift_1802_){
_start:
{
uint8_t v___x_427__boxed_1803_; uint8_t v___y_433__boxed_1804_; uint8_t v_____do__lift_434__boxed_1805_; lean_object* v_res_1806_; 
v___x_427__boxed_1803_ = lean_unbox(v___x_1794_);
v___y_433__boxed_1804_ = lean_unbox(v___y_1801_);
v_____do__lift_434__boxed_1805_ = lean_unbox(v_____do__lift_1802_);
v_res_1806_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1791_, v_n_1792_, v_toPure_1793_, v___x_427__boxed_1803_, v_inst_1795_, v_inst_1796_, v_inst_1797_, v_inst_1798_, v_inst_1799_, v_toBind_1800_, v___y_433__boxed_1804_, v_____do__lift_434__boxed_1805_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1807_, lean_object* v_toPure_1808_, uint8_t v___x_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_toBind_1815_, uint8_t v___y_1816_, lean_object* v___x_1817_, lean_object* v_env_1818_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = lean_box(v___x_1809_);
v___x_1820_ = lean_box(v___y_1816_);
lean_inc(v_toBind_1815_);
lean_inc_ref(v_inst_1812_);
lean_inc_ref(v_inst_1810_);
v___f_1821_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1821_, 0, v_env_1818_);
lean_closure_set(v___f_1821_, 1, v_n_1807_);
lean_closure_set(v___f_1821_, 2, v_toPure_1808_);
lean_closure_set(v___f_1821_, 3, v___x_1819_);
lean_closure_set(v___f_1821_, 4, v_inst_1810_);
lean_closure_set(v___f_1821_, 5, v_inst_1811_);
lean_closure_set(v___f_1821_, 6, v_inst_1812_);
lean_closure_set(v___f_1821_, 7, v_inst_1813_);
lean_closure_set(v___f_1821_, 8, v_inst_1814_);
lean_closure_set(v___f_1821_, 9, v_toBind_1815_);
lean_closure_set(v___f_1821_, 10, v___x_1820_);
v___x_1822_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1823_ = l_Lean_Option_getM___redArg(v_inst_1810_, v_inst_1812_, v___x_1817_, v___x_1822_);
v___x_1824_ = lean_apply_4(v_toBind_1815_, lean_box(0), lean_box(0), v___x_1823_, v___f_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1825_, lean_object* v_toPure_1826_, lean_object* v___x_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_toBind_1833_, lean_object* v___y_1834_, lean_object* v___x_1835_, lean_object* v_env_1836_){
_start:
{
uint8_t v___x_469__boxed_1837_; uint8_t v___y_475__boxed_1838_; lean_object* v_res_1839_; 
v___x_469__boxed_1837_ = lean_unbox(v___x_1827_);
v___y_475__boxed_1838_ = lean_unbox(v___y_1834_);
v_res_1839_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1825_, v_toPure_1826_, v___x_469__boxed_1837_, v_inst_1828_, v_inst_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v_toBind_1833_, v___y_475__boxed_1838_, v___x_1835_, v_env_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_n_1845_){
_start:
{
lean_object* v___x_1846_; uint8_t v___y_1848_; uint8_t v___x_1863_; 
v___x_1846_ = l_Lean_KVMap_instValueBool;
v___x_1863_ = l_Lean_isPrivateName(v_n_1845_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; 
v___x_1864_ = 1;
v___y_1848_ = v___x_1864_;
goto v___jp_1847_;
}
else
{
uint8_t v___x_1865_; 
v___x_1865_ = 0;
v___y_1848_ = v___x_1865_;
goto v___jp_1847_;
}
v___jp_1847_:
{
if (v___y_1848_ == 0)
{
lean_object* v_toApplicative_1849_; lean_object* v_toBind_1850_; lean_object* v_toPure_1851_; lean_object* v_getEnv_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___f_1856_; lean_object* v___x_1857_; 
v_toApplicative_1849_ = lean_ctor_get(v_inst_1842_, 0);
v_toBind_1850_ = lean_ctor_get(v_inst_1842_, 1);
lean_inc_n(v_toBind_1850_, 2);
v_toPure_1851_ = lean_ctor_get(v_toApplicative_1849_, 1);
lean_inc(v_toPure_1851_);
v_getEnv_1852_ = lean_ctor_get(v_inst_1843_, 0);
lean_inc(v_getEnv_1852_);
v___x_1853_ = 1;
v___x_1854_ = lean_box(v___x_1853_);
v___x_1855_ = lean_box(v___y_1848_);
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1856_, 0, v_n_1845_);
lean_closure_set(v___f_1856_, 1, v_toPure_1851_);
lean_closure_set(v___f_1856_, 2, v___x_1854_);
lean_closure_set(v___f_1856_, 3, v_inst_1842_);
lean_closure_set(v___f_1856_, 4, v_inst_1843_);
lean_closure_set(v___f_1856_, 5, v_inst_1844_);
lean_closure_set(v___f_1856_, 6, v_inst_1840_);
lean_closure_set(v___f_1856_, 7, v_inst_1841_);
lean_closure_set(v___f_1856_, 8, v_toBind_1850_);
lean_closure_set(v___f_1856_, 9, v___x_1855_);
lean_closure_set(v___f_1856_, 10, v___x_1846_);
v___x_1857_ = lean_apply_4(v_toBind_1850_, lean_box(0), lean_box(0), v_getEnv_1852_, v___f_1856_);
return v___x_1857_;
}
else
{
lean_object* v_toApplicative_1858_; lean_object* v_toPure_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_toApplicative_1858_ = lean_ctor_get(v_inst_1842_, 0);
lean_inc_ref(v_toApplicative_1858_);
lean_dec(v_n_1845_);
lean_dec_ref(v_inst_1844_);
lean_dec_ref(v_inst_1843_);
lean_dec_ref(v_inst_1842_);
lean_dec(v_inst_1841_);
lean_dec_ref(v_inst_1840_);
v_toPure_1859_ = lean_ctor_get(v_toApplicative_1858_, 1);
lean_inc(v_toPure_1859_);
lean_dec_ref(v_toApplicative_1858_);
v___x_1860_ = 0;
v___x_1861_ = lean_box(v___x_1860_);
v___x_1862_ = lean_apply_2(v_toPure_1859_, lean_box(0), v___x_1861_);
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_n_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1867_, v_inst_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_n_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1874_){
_start:
{
lean_object* v_fst_1875_; uint8_t v___x_1876_; 
v_fst_1875_ = lean_ctor_get(v_x_1874_, 0);
v___x_1876_ = l_Lean_isPrivateName(v_fst_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1877_);
lean_dec_ref(v_x_1877_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1880_, lean_object* v_res_1881_, lean_object* v_____r_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_apply_2(v_toPure_1880_, lean_box(0), v_res_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1884_, lean_object* v_toPure_1885_, lean_object* v_res_1886_, lean_object* v___f_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_toBind_1893_, lean_object* v___f_1894_, lean_object* v_____do__lift_1895_){
_start:
{
if (v_enableLog_1884_ == 0)
{
lean_object* v___x_1896_; 
lean_dec(v___f_1894_);
lean_dec(v_toBind_1893_);
lean_dec(v_inst_1892_);
lean_dec_ref(v_inst_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
lean_dec_ref(v___f_1887_);
v___x_1896_ = lean_apply_2(v_toPure_1885_, lean_box(0), v_res_1886_);
return v___x_1896_;
}
else
{
uint8_t v_isExporting_1897_; 
v_isExporting_1897_ = lean_ctor_get_uint8(v_____do__lift_1895_, sizeof(void*)*13);
if (v_isExporting_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec(v___f_1894_);
lean_dec(v_toBind_1893_);
lean_dec(v_inst_1892_);
lean_dec_ref(v_inst_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
lean_dec_ref(v___f_1887_);
v___x_1898_ = lean_apply_2(v_toPure_1885_, lean_box(0), v_res_1886_);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; 
lean_inc(v_res_1886_);
v___x_1899_ = l_List_find_x3f___redArg(v___f_1887_, v_res_1886_);
if (lean_obj_tag(v___x_1899_) == 1)
{
lean_object* v_val_1900_; lean_object* v_fst_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v_res_1886_);
lean_dec(v_toPure_1885_);
v_val_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v_fst_1901_ = lean_ctor_get(v_val_1900_, 0);
lean_inc(v_fst_1901_);
lean_dec(v_val_1900_);
v___x_1902_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1888_, v_inst_1889_, v_inst_1890_, v_inst_1891_, v_inst_1892_, v_fst_1901_);
v___x_1903_ = lean_apply_4(v_toBind_1893_, lean_box(0), lean_box(0), v___x_1902_, v___f_1894_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; 
lean_dec(v___x_1899_);
lean_dec(v___f_1894_);
lean_dec(v_toBind_1893_);
lean_dec(v_inst_1892_);
lean_dec_ref(v_inst_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1904_ = lean_apply_2(v_toPure_1885_, lean_box(0), v_res_1886_);
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1905_, lean_object* v_toPure_1906_, lean_object* v_res_1907_, lean_object* v___f_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_toBind_1914_, lean_object* v___f_1915_, lean_object* v_____do__lift_1916_){
_start:
{
uint8_t v_enableLog_boxed_1917_; lean_object* v_res_1918_; 
v_enableLog_boxed_1917_ = lean_unbox(v_enableLog_1905_);
v_res_1918_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1917_, v_toPure_1906_, v_res_1907_, v___f_1908_, v_inst_1909_, v_inst_1910_, v_inst_1911_, v_inst_1912_, v_inst_1913_, v_toBind_1914_, v___f_1915_, v_____do__lift_1916_);
lean_dec_ref(v_____do__lift_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1919_, lean_object* v_____do__lift_1920_, lean_object* v_____do__lift_1921_, lean_object* v_id_1922_, lean_object* v_toPure_1923_, uint8_t v_enableLog_1924_, lean_object* v___f_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_toBind_1931_, lean_object* v_getEnv_1932_, lean_object* v_____do__lift_1933_){
_start:
{
lean_object* v_res_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v_res_1934_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1919_, v_____do__lift_1920_, v_____do__lift_1921_, v_____do__lift_1933_, v_id_1922_);
lean_inc(v_res_1934_);
lean_inc(v_toPure_1923_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1935_, 0, v_toPure_1923_);
lean_closure_set(v___f_1935_, 1, v_res_1934_);
v___x_1936_ = lean_box(v_enableLog_1924_);
lean_inc(v_toBind_1931_);
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1937_, 0, v___x_1936_);
lean_closure_set(v___f_1937_, 1, v_toPure_1923_);
lean_closure_set(v___f_1937_, 2, v_res_1934_);
lean_closure_set(v___f_1937_, 3, v___f_1925_);
lean_closure_set(v___f_1937_, 4, v_inst_1926_);
lean_closure_set(v___f_1937_, 5, v_inst_1927_);
lean_closure_set(v___f_1937_, 6, v_inst_1928_);
lean_closure_set(v___f_1937_, 7, v_inst_1929_);
lean_closure_set(v___f_1937_, 8, v_inst_1930_);
lean_closure_set(v___f_1937_, 9, v_toBind_1931_);
lean_closure_set(v___f_1937_, 10, v___f_1935_);
v___x_1938_ = lean_apply_4(v_toBind_1931_, lean_box(0), lean_box(0), v_getEnv_1932_, v___f_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1939_, lean_object* v_____do__lift_1940_, lean_object* v_____do__lift_1941_, lean_object* v_id_1942_, lean_object* v_toPure_1943_, lean_object* v_enableLog_1944_, lean_object* v___f_1945_, lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_toBind_1951_, lean_object* v_getEnv_1952_, lean_object* v_____do__lift_1953_){
_start:
{
uint8_t v_enableLog_boxed_1954_; lean_object* v_res_1955_; 
v_enableLog_boxed_1954_ = lean_unbox(v_enableLog_1944_);
v_res_1955_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1939_, v_____do__lift_1940_, v_____do__lift_1941_, v_id_1942_, v_toPure_1943_, v_enableLog_boxed_1954_, v___f_1945_, v_inst_1946_, v_inst_1947_, v_inst_1948_, v_inst_1949_, v_inst_1950_, v_toBind_1951_, v_getEnv_1952_, v_____do__lift_1953_);
lean_dec_ref(v_____do__lift_1940_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1956_, lean_object* v_____do__lift_1957_, lean_object* v_id_1958_, lean_object* v_toPure_1959_, uint8_t v_enableLog_1960_, lean_object* v___f_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_toBind_1967_, lean_object* v_getEnv_1968_, lean_object* v_getOpenDecls_1969_, lean_object* v_____do__lift_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_box(v_enableLog_1960_);
lean_inc(v_toBind_1967_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1972_, 0, v_____do__lift_1956_);
lean_closure_set(v___f_1972_, 1, v_____do__lift_1957_);
lean_closure_set(v___f_1972_, 2, v_____do__lift_1970_);
lean_closure_set(v___f_1972_, 3, v_id_1958_);
lean_closure_set(v___f_1972_, 4, v_toPure_1959_);
lean_closure_set(v___f_1972_, 5, v___x_1971_);
lean_closure_set(v___f_1972_, 6, v___f_1961_);
lean_closure_set(v___f_1972_, 7, v_inst_1962_);
lean_closure_set(v___f_1972_, 8, v_inst_1963_);
lean_closure_set(v___f_1972_, 9, v_inst_1964_);
lean_closure_set(v___f_1972_, 10, v_inst_1965_);
lean_closure_set(v___f_1972_, 11, v_inst_1966_);
lean_closure_set(v___f_1972_, 12, v_toBind_1967_);
lean_closure_set(v___f_1972_, 13, v_getEnv_1968_);
v___x_1973_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v_getOpenDecls_1969_, v___f_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1974_, lean_object* v_____do__lift_1975_, lean_object* v_id_1976_, lean_object* v_toPure_1977_, lean_object* v_enableLog_1978_, lean_object* v___f_1979_, lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_toBind_1985_, lean_object* v_getEnv_1986_, lean_object* v_getOpenDecls_1987_, lean_object* v_____do__lift_1988_){
_start:
{
uint8_t v_enableLog_boxed_1989_; lean_object* v_res_1990_; 
v_enableLog_boxed_1989_ = lean_unbox(v_enableLog_1978_);
v_res_1990_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1974_, v_____do__lift_1975_, v_id_1976_, v_toPure_1977_, v_enableLog_boxed_1989_, v___f_1979_, v_inst_1980_, v_inst_1981_, v_inst_1982_, v_inst_1983_, v_inst_1984_, v_toBind_1985_, v_getEnv_1986_, v_getOpenDecls_1987_, v_____do__lift_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1991_, lean_object* v_____do__lift_1992_, lean_object* v_id_1993_, lean_object* v_toPure_1994_, uint8_t v_enableLog_1995_, lean_object* v___f_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_toBind_2002_, lean_object* v_getEnv_2003_, lean_object* v_____do__lift_2004_){
_start:
{
lean_object* v_getCurrNamespace_2005_; lean_object* v_getOpenDecls_2006_; lean_object* v___x_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; 
v_getCurrNamespace_2005_ = lean_ctor_get(v_inst_1991_, 0);
lean_inc(v_getCurrNamespace_2005_);
v_getOpenDecls_2006_ = lean_ctor_get(v_inst_1991_, 1);
lean_inc(v_getOpenDecls_2006_);
lean_dec_ref(v_inst_1991_);
v___x_2007_ = lean_box(v_enableLog_1995_);
lean_inc(v_toBind_2002_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_2008_, 0, v_____do__lift_1992_);
lean_closure_set(v___f_2008_, 1, v_____do__lift_2004_);
lean_closure_set(v___f_2008_, 2, v_id_1993_);
lean_closure_set(v___f_2008_, 3, v_toPure_1994_);
lean_closure_set(v___f_2008_, 4, v___x_2007_);
lean_closure_set(v___f_2008_, 5, v___f_1996_);
lean_closure_set(v___f_2008_, 6, v_inst_1997_);
lean_closure_set(v___f_2008_, 7, v_inst_1998_);
lean_closure_set(v___f_2008_, 8, v_inst_1999_);
lean_closure_set(v___f_2008_, 9, v_inst_2000_);
lean_closure_set(v___f_2008_, 10, v_inst_2001_);
lean_closure_set(v___f_2008_, 11, v_toBind_2002_);
lean_closure_set(v___f_2008_, 12, v_getEnv_2003_);
lean_closure_set(v___f_2008_, 13, v_getOpenDecls_2006_);
v___x_2009_ = lean_apply_4(v_toBind_2002_, lean_box(0), lean_box(0), v_getCurrNamespace_2005_, v___f_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_2010_, lean_object* v_____do__lift_2011_, lean_object* v_id_2012_, lean_object* v_toPure_2013_, lean_object* v_enableLog_2014_, lean_object* v___f_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_toBind_2021_, lean_object* v_getEnv_2022_, lean_object* v_____do__lift_2023_){
_start:
{
uint8_t v_enableLog_boxed_2024_; lean_object* v_res_2025_; 
v_enableLog_boxed_2024_ = lean_unbox(v_enableLog_2014_);
v_res_2025_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_2010_, v_____do__lift_2011_, v_id_2012_, v_toPure_2013_, v_enableLog_boxed_2024_, v___f_2015_, v_inst_2016_, v_inst_2017_, v_inst_2018_, v_inst_2019_, v_inst_2020_, v_toBind_2021_, v_getEnv_2022_, v_____do__lift_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_id_2028_, lean_object* v_toPure_2029_, uint8_t v_enableLog_2030_, lean_object* v___f_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_toBind_2036_, lean_object* v_getEnv_2037_, lean_object* v_____do__lift_2038_){
_start:
{
lean_object* v_getOptions_2039_; lean_object* v___x_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; 
v_getOptions_2039_ = lean_ctor_get(v_inst_2026_, 0);
lean_inc(v_getOptions_2039_);
v___x_2040_ = lean_box(v_enableLog_2030_);
lean_inc(v_toBind_2036_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_2041_, 0, v_inst_2027_);
lean_closure_set(v___f_2041_, 1, v_____do__lift_2038_);
lean_closure_set(v___f_2041_, 2, v_id_2028_);
lean_closure_set(v___f_2041_, 3, v_toPure_2029_);
lean_closure_set(v___f_2041_, 4, v___x_2040_);
lean_closure_set(v___f_2041_, 5, v___f_2031_);
lean_closure_set(v___f_2041_, 6, v_inst_2032_);
lean_closure_set(v___f_2041_, 7, v_inst_2033_);
lean_closure_set(v___f_2041_, 8, v_inst_2026_);
lean_closure_set(v___f_2041_, 9, v_inst_2034_);
lean_closure_set(v___f_2041_, 10, v_inst_2035_);
lean_closure_set(v___f_2041_, 11, v_toBind_2036_);
lean_closure_set(v___f_2041_, 12, v_getEnv_2037_);
v___x_2042_ = lean_apply_4(v_toBind_2036_, lean_box(0), lean_box(0), v_getOptions_2039_, v___f_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_id_2045_, lean_object* v_toPure_2046_, lean_object* v_enableLog_2047_, lean_object* v___f_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_toBind_2053_, lean_object* v_getEnv_2054_, lean_object* v_____do__lift_2055_){
_start:
{
uint8_t v_enableLog_boxed_2056_; lean_object* v_res_2057_; 
v_enableLog_boxed_2056_ = lean_unbox(v_enableLog_2047_);
v_res_2057_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2043_, v_inst_2044_, v_id_2045_, v_toPure_2046_, v_enableLog_boxed_2056_, v___f_2048_, v_inst_2049_, v_inst_2050_, v_inst_2051_, v_inst_2052_, v_toBind_2053_, v_getEnv_2054_, v_____do__lift_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_id_2065_, uint8_t v_enableLog_2066_){
_start:
{
lean_object* v_toApplicative_2067_; lean_object* v_toBind_2068_; lean_object* v_getEnv_2069_; lean_object* v_toPure_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; 
v_toApplicative_2067_ = lean_ctor_get(v_inst_2059_, 0);
v_toBind_2068_ = lean_ctor_get(v_inst_2059_, 1);
lean_inc_n(v_toBind_2068_, 2);
v_getEnv_2069_ = lean_ctor_get(v_inst_2061_, 0);
lean_inc_n(v_getEnv_2069_, 2);
v_toPure_2070_ = lean_ctor_get(v_toApplicative_2067_, 1);
lean_inc(v_toPure_2070_);
v___f_2071_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2072_ = lean_box(v_enableLog_2066_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2073_, 0, v_inst_2062_);
lean_closure_set(v___f_2073_, 1, v_inst_2060_);
lean_closure_set(v___f_2073_, 2, v_id_2065_);
lean_closure_set(v___f_2073_, 3, v_toPure_2070_);
lean_closure_set(v___f_2073_, 4, v___x_2072_);
lean_closure_set(v___f_2073_, 5, v___f_2071_);
lean_closure_set(v___f_2073_, 6, v_inst_2059_);
lean_closure_set(v___f_2073_, 7, v_inst_2061_);
lean_closure_set(v___f_2073_, 8, v_inst_2063_);
lean_closure_set(v___f_2073_, 9, v_inst_2064_);
lean_closure_set(v___f_2073_, 10, v_toBind_2068_);
lean_closure_set(v___f_2073_, 11, v_getEnv_2069_);
v___x_2074_ = lean_apply_4(v_toBind_2068_, lean_box(0), lean_box(0), v_getEnv_2069_, v___f_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_id_2081_, lean_object* v_enableLog_2082_){
_start:
{
uint8_t v_enableLog_boxed_2083_; lean_object* v_res_2084_; 
v_enableLog_boxed_2083_ = lean_unbox(v_enableLog_2082_);
v_res_2084_ = l_Lean_resolveGlobalName___redArg(v_inst_2075_, v_inst_2076_, v_inst_2077_, v_inst_2078_, v_inst_2079_, v_inst_2080_, v_id_2081_, v_enableLog_boxed_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_id_2092_, uint8_t v_enableLog_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_resolveGlobalName___redArg(v_inst_2086_, v_inst_2087_, v_inst_2088_, v_inst_2089_, v_inst_2090_, v_inst_2091_, v_id_2092_, v_enableLog_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_id_2102_, lean_object* v_enableLog_2103_){
_start:
{
uint8_t v_enableLog_boxed_2104_; lean_object* v_res_2105_; 
v_enableLog_boxed_2104_ = lean_unbox(v_enableLog_2103_);
v_res_2105_ = l_Lean_resolveGlobalName(v_m_2095_, v_inst_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_inst_2100_, v_inst_2101_, v_id_2102_, v_enableLog_boxed_2104_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2106_, lean_object* v_nss_2107_, lean_object* v_____r_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_apply_2(v_toPure_2106_, lean_box(0), v_nss_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2112_, lean_object* v_____do__lift_2113_, lean_object* v_id_2114_, uint8_t v_allowEmpty_2115_, lean_object* v_toPure_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_toBind_2119_, lean_object* v_____do__lift_2120_){
_start:
{
lean_object* v_nss_2121_; 
lean_inc(v_id_2114_);
v_nss_2121_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2112_, v_____do__lift_2113_, v_____do__lift_2120_, v_id_2114_);
if (v_allowEmpty_2115_ == 0)
{
uint8_t v___x_2122_; 
v___x_2122_ = l_List_isEmpty___redArg(v_nss_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v_toBind_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_inst_2117_);
lean_dec(v_id_2114_);
v___x_2123_ = lean_apply_2(v_toPure_2116_, lean_box(0), v_nss_2121_);
return v___x_2123_;
}
else
{
lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___f_2124_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2124_, 0, v_toPure_2116_);
lean_closure_set(v___f_2124_, 1, v_nss_2121_);
v___x_2125_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2114_, v___x_2122_);
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2129_ = lean_string_append(v___x_2127_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = l_Lean_MessageData_ofFormat(v___x_2130_);
v___x_2132_ = l_Lean_throwError___redArg(v_inst_2117_, v_inst_2118_, v___x_2131_);
v___x_2133_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2132_, v___f_2124_);
return v___x_2133_;
}
}
else
{
lean_object* v___x_2134_; 
lean_dec(v_toBind_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_inst_2117_);
lean_dec(v_id_2114_);
v___x_2134_ = lean_apply_2(v_toPure_2116_, lean_box(0), v_nss_2121_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2135_, lean_object* v_____do__lift_2136_, lean_object* v_id_2137_, lean_object* v_allowEmpty_2138_, lean_object* v_toPure_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_toBind_2142_, lean_object* v_____do__lift_2143_){
_start:
{
uint8_t v_allowEmpty_boxed_2144_; lean_object* v_res_2145_; 
v_allowEmpty_boxed_2144_ = lean_unbox(v_allowEmpty_2138_);
v_res_2145_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2135_, v_____do__lift_2136_, v_id_2137_, v_allowEmpty_boxed_2144_, v_toPure_2139_, v_inst_2140_, v_inst_2141_, v_toBind_2142_, v_____do__lift_2143_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2146_, lean_object* v_id_2147_, uint8_t v_allowEmpty_2148_, lean_object* v_toPure_2149_, lean_object* v_inst_2150_, lean_object* v_inst_2151_, lean_object* v_toBind_2152_, lean_object* v_getOpenDecls_2153_, lean_object* v_____do__lift_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(v_allowEmpty_2148_);
lean_inc(v_toBind_2152_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2156_, 0, v_____do__lift_2146_);
lean_closure_set(v___f_2156_, 1, v_____do__lift_2154_);
lean_closure_set(v___f_2156_, 2, v_id_2147_);
lean_closure_set(v___f_2156_, 3, v___x_2155_);
lean_closure_set(v___f_2156_, 4, v_toPure_2149_);
lean_closure_set(v___f_2156_, 5, v_inst_2150_);
lean_closure_set(v___f_2156_, 6, v_inst_2151_);
lean_closure_set(v___f_2156_, 7, v_toBind_2152_);
v___x_2157_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v_getOpenDecls_2153_, v___f_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2158_, lean_object* v_id_2159_, lean_object* v_allowEmpty_2160_, lean_object* v_toPure_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_toBind_2164_, lean_object* v_getOpenDecls_2165_, lean_object* v_____do__lift_2166_){
_start:
{
uint8_t v_allowEmpty_boxed_2167_; lean_object* v_res_2168_; 
v_allowEmpty_boxed_2167_ = lean_unbox(v_allowEmpty_2160_);
v_res_2168_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2158_, v_id_2159_, v_allowEmpty_boxed_2167_, v_toPure_2161_, v_inst_2162_, v_inst_2163_, v_toBind_2164_, v_getOpenDecls_2165_, v_____do__lift_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2169_, lean_object* v_id_2170_, uint8_t v_allowEmpty_2171_, lean_object* v_toPure_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_toBind_2175_, lean_object* v_____do__lift_2176_){
_start:
{
lean_object* v_getCurrNamespace_2177_; lean_object* v_getOpenDecls_2178_; lean_object* v___x_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; 
v_getCurrNamespace_2177_ = lean_ctor_get(v_inst_2169_, 0);
lean_inc(v_getCurrNamespace_2177_);
v_getOpenDecls_2178_ = lean_ctor_get(v_inst_2169_, 1);
lean_inc(v_getOpenDecls_2178_);
lean_dec_ref(v_inst_2169_);
v___x_2179_ = lean_box(v_allowEmpty_2171_);
lean_inc(v_toBind_2175_);
v___f_2180_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2180_, 0, v_____do__lift_2176_);
lean_closure_set(v___f_2180_, 1, v_id_2170_);
lean_closure_set(v___f_2180_, 2, v___x_2179_);
lean_closure_set(v___f_2180_, 3, v_toPure_2172_);
lean_closure_set(v___f_2180_, 4, v_inst_2173_);
lean_closure_set(v___f_2180_, 5, v_inst_2174_);
lean_closure_set(v___f_2180_, 6, v_toBind_2175_);
lean_closure_set(v___f_2180_, 7, v_getOpenDecls_2178_);
v___x_2181_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v_getCurrNamespace_2177_, v___f_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2182_, lean_object* v_id_2183_, lean_object* v_allowEmpty_2184_, lean_object* v_toPure_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_toBind_2188_, lean_object* v_____do__lift_2189_){
_start:
{
uint8_t v_allowEmpty_boxed_2190_; lean_object* v_res_2191_; 
v_allowEmpty_boxed_2190_ = lean_unbox(v_allowEmpty_2184_);
v_res_2191_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2182_, v_id_2183_, v_allowEmpty_boxed_2190_, v_toPure_2185_, v_inst_2186_, v_inst_2187_, v_toBind_2188_, v_____do__lift_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_inst_2195_, lean_object* v_id_2196_, uint8_t v_allowEmpty_2197_){
_start:
{
lean_object* v_toApplicative_2198_; lean_object* v_toBind_2199_; lean_object* v_getEnv_2200_; lean_object* v_toPure_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
v_toApplicative_2198_ = lean_ctor_get(v_inst_2192_, 0);
v_toBind_2199_ = lean_ctor_get(v_inst_2192_, 1);
lean_inc_n(v_toBind_2199_, 2);
v_getEnv_2200_ = lean_ctor_get(v_inst_2194_, 0);
lean_inc(v_getEnv_2200_);
lean_dec_ref(v_inst_2194_);
v_toPure_2201_ = lean_ctor_get(v_toApplicative_2198_, 1);
lean_inc(v_toPure_2201_);
v___x_2202_ = lean_box(v_allowEmpty_2197_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2203_, 0, v_inst_2193_);
lean_closure_set(v___f_2203_, 1, v_id_2196_);
lean_closure_set(v___f_2203_, 2, v___x_2202_);
lean_closure_set(v___f_2203_, 3, v_toPure_2201_);
lean_closure_set(v___f_2203_, 4, v_inst_2192_);
lean_closure_set(v___f_2203_, 5, v_inst_2195_);
lean_closure_set(v___f_2203_, 6, v_toBind_2199_);
v___x_2204_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v_getEnv_2200_, v___f_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_id_2209_, lean_object* v_allowEmpty_2210_){
_start:
{
uint8_t v_allowEmpty_boxed_2211_; lean_object* v_res_2212_; 
v_allowEmpty_boxed_2211_ = lean_unbox(v_allowEmpty_2210_);
v_res_2212_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_, v_id_2209_, v_allowEmpty_boxed_2211_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_id_2218_, uint8_t v_allowEmpty_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2214_, v_inst_2215_, v_inst_2216_, v_inst_2217_, v_id_2218_, v_allowEmpty_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_id_2226_, lean_object* v_allowEmpty_2227_){
_start:
{
uint8_t v_allowEmpty_boxed_2228_; lean_object* v_res_2229_; 
v_allowEmpty_boxed_2228_ = lean_unbox(v_allowEmpty_2227_);
v_res_2229_ = l_Lean_resolveNamespaceCore(v_m_2221_, v_inst_2222_, v_inst_2223_, v_inst_2224_, v_inst_2225_, v_id_2226_, v_allowEmpty_boxed_2228_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 0)
{
lean_object* v_ns_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_ns_2231_ = lean_ctor_get(v_x_2230_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_x_2230_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v_x_2230_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_ns_2231_);
lean_dec(v_x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 1);
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_ns_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v___x_2239_; 
lean_dec_ref(v_x_2230_);
v___x_2239_ = lean_box(0);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2240_, lean_object* v_withRef_2241_, lean_object* v___x_2242_, lean_object* v_oldRef_2243_){
_start:
{
lean_object* v_ref_2244_; lean_object* v___x_2245_; 
v_ref_2244_ = l_Lean_replaceRef(v_x_2240_, v_oldRef_2243_);
v___x_2245_ = lean_apply_3(v_withRef_2241_, lean_box(0), v_ref_2244_, v___x_2242_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2246_, lean_object* v_withRef_2247_, lean_object* v___x_2248_, lean_object* v_oldRef_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2246_, v_withRef_2247_, v___x_2248_, v_oldRef_2249_);
lean_dec(v_oldRef_2249_);
lean_dec(v_x_2246_);
return v_res_2250_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2258_ = l_Lean_MessageData_ofFormat(v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_x_2263_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 3)
{
lean_object* v_toApplicative_2264_; lean_object* v_toBind_2265_; lean_object* v_toPure_2266_; lean_object* v_toMonadRef_2267_; lean_object* v_val_2268_; lean_object* v_preresolved_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v_pre_2272_; uint8_t v___x_2273_; 
v_toApplicative_2264_ = lean_ctor_get(v_inst_2259_, 0);
v_toBind_2265_ = lean_ctor_get(v_inst_2259_, 1);
lean_inc(v_toBind_2265_);
v_toPure_2266_ = lean_ctor_get(v_toApplicative_2264_, 1);
v_toMonadRef_2267_ = lean_ctor_get(v_inst_2262_, 1);
v_val_2268_ = lean_ctor_get(v_x_2263_, 2);
v_preresolved_2269_ = lean_ctor_get(v_x_2263_, 3);
v___f_2270_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2271_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2269_);
v_pre_2272_ = l_List_filterMapTR_go___redArg(v___f_2270_, v_preresolved_2269_, v___x_2271_);
v___x_2273_ = l_List_isEmpty___redArg(v_pre_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_inc(v_toPure_2266_);
lean_dec(v_toBind_2265_);
lean_dec_ref_known(v_x_2263_, 4);
lean_dec_ref(v_inst_2262_);
lean_dec_ref(v_inst_2261_);
lean_dec_ref(v_inst_2260_);
lean_dec_ref(v_inst_2259_);
v___x_2274_ = lean_apply_2(v_toPure_2266_, lean_box(0), v_pre_2272_);
return v___x_2274_;
}
else
{
lean_object* v_getRef_2275_; lean_object* v_withRef_2276_; uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; 
lean_dec(v_pre_2272_);
v_getRef_2275_ = lean_ctor_get(v_toMonadRef_2267_, 0);
lean_inc(v_getRef_2275_);
v_withRef_2276_ = lean_ctor_get(v_toMonadRef_2267_, 1);
lean_inc(v_withRef_2276_);
v___x_2277_ = 0;
lean_inc(v_val_2268_);
v___x_2278_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2259_, v_inst_2260_, v_inst_2261_, v_inst_2262_, v_val_2268_, v___x_2277_);
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2279_, 0, v_x_2263_);
lean_closure_set(v___f_2279_, 1, v_withRef_2276_);
lean_closure_set(v___f_2279_, 2, v___x_2278_);
v___x_2280_ = lean_apply_4(v_toBind_2265_, lean_box(0), lean_box(0), v_getRef_2275_, v___f_2279_);
return v___x_2280_;
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec_ref(v_inst_2261_);
lean_dec_ref(v_inst_2260_);
v___x_2281_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2282_ = l_Lean_throwErrorAt___redArg(v_inst_2259_, v_inst_2262_, v_x_2263_, v___x_2281_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2283_, lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_resolveNamespace___redArg(v_inst_2284_, v_inst_2285_, v_inst_2286_, v_inst_2287_, v_x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2292_, lean_object* v___f_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_toPure_2296_, lean_object* v_____do__lift_2297_){
_start:
{
if (lean_obj_tag(v_____do__lift_2297_) == 1)
{
lean_object* v_tail_2313_; 
v_tail_2313_ = lean_ctor_get(v_____do__lift_2297_, 1);
if (lean_obj_tag(v_tail_2313_) == 0)
{
lean_object* v_head_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
lean_dec_ref(v___f_2293_);
v_head_2314_ = lean_ctor_get(v_____do__lift_2297_, 0);
lean_inc(v_head_2314_);
lean_dec_ref_known(v_____do__lift_2297_, 2);
v___x_2315_ = lean_apply_2(v_toPure_2296_, lean_box(0), v_head_2314_);
return v___x_2315_;
}
else
{
lean_dec(v_toPure_2296_);
goto v___jp_2298_;
}
}
else
{
lean_dec(v_toPure_2296_);
goto v___jp_2298_;
}
v___jp_2298_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2299_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2300_ = l_Lean_TSyntax_getId(v_id_2292_);
v___x_2301_ = 1;
v___x_2302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2300_, v___x_2301_);
v___x_2303_ = lean_string_append(v___x_2299_, v___x_2302_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2305_ = lean_string_append(v___x_2303_, v___x_2304_);
v___x_2306_ = l_List_toString___redArg(v___f_2293_, v_____do__lift_2297_);
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
v___x_2310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
v___x_2311_ = l_Lean_MessageData_ofFormat(v___x_2310_);
v___x_2312_ = l_Lean_throwError___redArg(v_inst_2294_, v_inst_2295_, v___x_2311_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2316_, lean_object* v___f_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_toPure_2320_, lean_object* v_____do__lift_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2316_, v___f_2317_, v_inst_2318_, v_inst_2319_, v_toPure_2320_, v_____do__lift_2321_);
lean_dec(v_id_2316_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_id_2328_){
_start:
{
lean_object* v_toApplicative_2329_; lean_object* v_toBind_2330_; lean_object* v_toPure_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v_toApplicative_2329_ = lean_ctor_get(v_inst_2324_, 0);
v_toBind_2330_ = lean_ctor_get(v_inst_2324_, 1);
lean_inc(v_toBind_2330_);
v_toPure_2331_ = lean_ctor_get(v_toApplicative_2329_, 1);
lean_inc(v_toPure_2331_);
v___f_2332_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2328_);
lean_inc_ref(v_inst_2327_);
lean_inc_ref(v_inst_2324_);
v___x_2333_ = l_Lean_resolveNamespace___redArg(v_inst_2324_, v_inst_2325_, v_inst_2326_, v_inst_2327_, v_id_2328_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2334_, 0, v_id_2328_);
lean_closure_set(v___f_2334_, 1, v___f_2332_);
lean_closure_set(v___f_2334_, 2, v_inst_2324_);
lean_closure_set(v___f_2334_, 3, v_inst_2327_);
lean_closure_set(v___f_2334_, 4, v_toPure_2331_);
v___x_2335_ = lean_apply_4(v_toBind_2330_, lean_box(0), lean_box(0), v___x_2333_, v___f_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_id_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_inst_2340_, v_id_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2343_){
_start:
{
lean_object* v_snd_2344_; uint8_t v___x_2345_; 
v_snd_2344_ = lean_ctor_get(v_x_2343_, 1);
v___x_2345_ = l_List_isEmpty___redArg(v_snd_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2346_){
_start:
{
uint8_t v_res_2347_; lean_object* v_r_2348_; 
v_res_2347_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2346_);
lean_dec_ref(v_x_2346_);
v_r_2348_ = lean_box(v_res_2347_);
return v_r_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2349_){
_start:
{
lean_object* v_fst_2350_; 
v_fst_2350_ = lean_ctor_get(v_x_2349_, 0);
lean_inc(v_fst_2350_);
return v_fst_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2351_);
lean_dec_ref(v_x_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2353_, lean_object* v_cs_2354_, lean_object* v_toPure_2355_, lean_object* v_____r_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = l_List_mapTR_loop___redArg(v___f_2353_, v_cs_2354_, v___x_2357_);
v___x_2359_ = lean_apply_2(v_toPure_2355_, lean_box(0), v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2360_, lean_object* v_____r_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_apply_1(v___f_2360_, v_____r_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_n_2366_, lean_object* v_toBind_2367_, lean_object* v___f_2368_, lean_object* v_____do__lift_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2363_, v_inst_2364_, v_inst_2365_, v_____do__lift_2369_, v_n_2366_);
v___x_2371_ = lean_apply_4(v_toBind_2367_, lean_box(0), lean_box(0), v___x_2370_, v___f_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_n_2377_, lean_object* v_cs_2378_){
_start:
{
lean_object* v_toApplicative_2379_; lean_object* v_toBind_2380_; lean_object* v_toPure_2381_; lean_object* v_toMonadRef_2382_; lean_object* v___f_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v_cs_2386_; lean_object* v___f_2387_; uint8_t v___x_2388_; 
v_toApplicative_2379_ = lean_ctor_get(v_inst_2374_, 0);
v_toBind_2380_ = lean_ctor_get(v_inst_2374_, 1);
lean_inc(v_toBind_2380_);
v_toPure_2381_ = lean_ctor_get(v_toApplicative_2379_, 1);
v_toMonadRef_2382_ = lean_ctor_get(v_inst_2376_, 1);
v___f_2383_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2384_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2385_ = lean_box(0);
v_cs_2386_ = l_List_filterTR_loop___redArg(v___f_2383_, v_cs_2378_, v___x_2385_);
lean_inc(v_toPure_2381_);
lean_inc(v_cs_2386_);
v___f_2387_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2387_, 0, v___f_2384_);
lean_closure_set(v___f_2387_, 1, v_cs_2386_);
lean_closure_set(v___f_2387_, 2, v_toPure_2381_);
v___x_2388_ = l_List_isEmpty___redArg(v_cs_2386_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_inc(v_toPure_2381_);
lean_dec_ref(v___f_2387_);
lean_dec(v_toBind_2380_);
lean_dec(v_n_2377_);
lean_dec_ref(v_inst_2376_);
lean_dec_ref(v_inst_2375_);
lean_dec_ref(v_inst_2374_);
v___x_2389_ = lean_box(0);
v___x_2390_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2384_, v_cs_2386_, v_toPure_2381_, v___x_2389_);
return v___x_2390_;
}
else
{
lean_object* v_getRef_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; 
lean_dec(v_cs_2386_);
v_getRef_2391_ = lean_ctor_get(v_toMonadRef_2382_, 0);
lean_inc(v_getRef_2391_);
v___f_2392_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2392_, 0, v___f_2387_);
lean_inc(v_toBind_2380_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2393_, 0, v_inst_2374_);
lean_closure_set(v___f_2393_, 1, v_inst_2375_);
lean_closure_set(v___f_2393_, 2, v_inst_2376_);
lean_closure_set(v___f_2393_, 3, v_n_2377_);
lean_closure_set(v___f_2393_, 4, v_toBind_2380_);
lean_closure_set(v___f_2393_, 5, v___f_2392_);
v___x_2394_ = lean_apply_4(v_toBind_2380_, lean_box(0), lean_box(0), v_getRef_2391_, v___f_2393_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_n_2399_, lean_object* v_cs_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_filterFieldList___redArg(v_inst_2396_, v_inst_2397_, v_inst_2398_, v_n_2399_, v_cs_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_inst_2404_, lean_object* v_n_2405_, lean_object* v_cs_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_filterFieldList___redArg(v_inst_2402_, v_inst_2403_, v_inst_2404_, v_n_2405_, v_cs_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_, lean_object* v_n_2415_){
_start:
{
lean_object* v_toBind_2416_; lean_object* v___f_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_toBind_2416_ = lean_ctor_get(v_inst_2408_, 1);
lean_inc(v_toBind_2416_);
lean_inc(v_n_2415_);
lean_inc_ref(v_inst_2410_);
lean_inc_ref(v_inst_2408_);
v___f_2417_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2417_, 0, v_inst_2408_);
lean_closure_set(v___f_2417_, 1, v_inst_2410_);
lean_closure_set(v___f_2417_, 2, v_inst_2414_);
lean_closure_set(v___f_2417_, 3, v_n_2415_);
v___x_2418_ = 1;
v___x_2419_ = l_Lean_resolveGlobalName___redArg(v_inst_2408_, v_inst_2409_, v_inst_2410_, v_inst_2411_, v_inst_2412_, v_inst_2413_, v_n_2415_, v___x_2418_);
v___x_2420_ = lean_apply_4(v_toBind_2416_, lean_box(0), lean_box(0), v___x_2419_, v___f_2417_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_n_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2422_, v_inst_2423_, v_inst_2424_, v_inst_2425_, v_inst_2426_, v_inst_2427_, v_inst_2428_, v_n_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_box(0);
v___x_2433_ = l_Lean_mkConst(v_declName_2431_, v___x_2432_);
return v___x_2433_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_n_2444_, lean_object* v_cs_2445_){
_start:
{
lean_object* v_toApplicative_2446_; lean_object* v_toPure_2447_; lean_object* v___f_2448_; 
v_toApplicative_2446_ = lean_ctor_get(v_inst_2442_, 0);
v_toPure_2447_ = lean_ctor_get(v_toApplicative_2446_, 1);
v___f_2448_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2445_) == 1)
{
lean_object* v_tail_2462_; 
v_tail_2462_ = lean_ctor_get(v_cs_2445_, 1);
if (lean_obj_tag(v_tail_2462_) == 0)
{
lean_object* v_head_2463_; lean_object* v___x_2464_; 
lean_inc(v_toPure_2447_);
lean_dec(v_n_2444_);
lean_dec_ref(v_inst_2443_);
lean_dec_ref(v_inst_2442_);
v_head_2463_ = lean_ctor_get(v_cs_2445_, 0);
lean_inc(v_head_2463_);
lean_dec_ref_known(v_cs_2445_, 2);
v___x_2464_ = lean_apply_2(v_toPure_2447_, lean_box(0), v_head_2463_);
return v___x_2464_;
}
else
{
goto v___jp_2449_;
}
}
else
{
goto v___jp_2449_;
}
v___jp_2449_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2450_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2451_ = l_Lean_MessageData_ofName(v_n_2444_);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_box(0);
v___x_2456_ = l_List_mapTR_loop___redArg(v___f_2448_, v_cs_2445_, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2458_ = l_List_mapTR_loop___redArg(v___x_2457_, v___x_2456_, v___x_2455_);
v___x_2459_ = l_Lean_MessageData_ofList(v___x_2458_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2454_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l_Lean_throwError___redArg(v_inst_2442_, v_inst_2443_, v___x_2460_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_n_2468_, lean_object* v_cs_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_ensureNoOverload___redArg(v_inst_2466_, v_inst_2467_, v_n_2468_, v_cs_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_n_2473_, lean_object* v_____do__lift_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_ensureNoOverload___redArg(v_inst_2471_, v_inst_2472_, v_n_2473_, v_____do__lift_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_n_2483_){
_start:
{
lean_object* v_toBind_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_toBind_2484_ = lean_ctor_get(v_inst_2476_, 1);
lean_inc(v_toBind_2484_);
lean_inc(v_n_2483_);
lean_inc_ref(v_inst_2482_);
lean_inc_ref(v_inst_2476_);
v___f_2485_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2485_, 0, v_inst_2476_);
lean_closure_set(v___f_2485_, 1, v_inst_2482_);
lean_closure_set(v___f_2485_, 2, v_n_2483_);
v___x_2486_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2476_, v_inst_2477_, v_inst_2478_, v_inst_2479_, v_inst_2480_, v_inst_2481_, v_inst_2482_, v_n_2483_);
v___x_2487_ = lean_apply_4(v_toBind_2484_, lean_box(0), lean_box(0), v___x_2486_, v___f_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_n_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2489_, v_inst_2490_, v_inst_2491_, v_inst_2492_, v_inst_2493_, v_inst_2494_, v_inst_2495_, v_n_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2498_){
_start:
{
if (lean_obj_tag(v_x_2498_) == 1)
{
lean_object* v_fields_2499_; 
v_fields_2499_ = lean_ctor_get(v_x_2498_, 1);
if (lean_obj_tag(v_fields_2499_) == 0)
{
lean_object* v_n_2500_; lean_object* v___x_2501_; 
v_n_2500_ = lean_ctor_get(v_x_2498_, 0);
lean_inc(v_n_2500_);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_n_2500_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_box(0);
return v___x_2502_;
}
}
else
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_box(0);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2504_);
lean_dec_ref(v_x_2504_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2506_, lean_object* v_withRef_2507_, lean_object* v___x_2508_, lean_object* v_oldRef_2509_){
_start:
{
lean_object* v_ref_2510_; lean_object* v___x_2511_; 
v_ref_2510_ = l_Lean_replaceRef(v_stx_2506_, v_oldRef_2509_);
v___x_2511_ = lean_apply_3(v_withRef_2507_, lean_box(0), v_ref_2510_, v___x_2508_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2512_, lean_object* v_withRef_2513_, lean_object* v___x_2514_, lean_object* v_oldRef_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2512_, v_withRef_2513_, v___x_2514_, v_oldRef_2515_);
lean_dec(v_oldRef_2515_);
lean_dec(v_stx_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_stx_2520_, lean_object* v_k_2521_){
_start:
{
if (lean_obj_tag(v_stx_2520_) == 3)
{
lean_object* v_toApplicative_2522_; lean_object* v_toBind_2523_; lean_object* v_toPure_2524_; lean_object* v_toMonadRef_2525_; lean_object* v_val_2526_; lean_object* v_preresolved_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v_pre_2530_; uint8_t v___x_2531_; 
v_toApplicative_2522_ = lean_ctor_get(v_inst_2518_, 0);
lean_inc_ref(v_toApplicative_2522_);
v_toBind_2523_ = lean_ctor_get(v_inst_2518_, 1);
lean_inc(v_toBind_2523_);
lean_dec_ref(v_inst_2518_);
v_toPure_2524_ = lean_ctor_get(v_toApplicative_2522_, 1);
lean_inc(v_toPure_2524_);
lean_dec_ref(v_toApplicative_2522_);
v_toMonadRef_2525_ = lean_ctor_get(v_inst_2519_, 1);
lean_inc_ref(v_toMonadRef_2525_);
lean_dec_ref(v_inst_2519_);
v_val_2526_ = lean_ctor_get(v_stx_2520_, 2);
v_preresolved_2527_ = lean_ctor_get(v_stx_2520_, 3);
v___f_2528_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2529_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2527_);
v_pre_2530_ = l_List_filterMapTR_go___redArg(v___f_2528_, v_preresolved_2527_, v___x_2529_);
v___x_2531_ = l_List_isEmpty___redArg(v_pre_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_dec_ref(v_toMonadRef_2525_);
lean_dec_ref_known(v_stx_2520_, 4);
lean_dec(v_toBind_2523_);
lean_dec(v_k_2521_);
v___x_2532_ = lean_apply_2(v_toPure_2524_, lean_box(0), v_pre_2530_);
return v___x_2532_;
}
else
{
lean_object* v_getRef_2533_; lean_object* v_withRef_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; 
lean_dec(v_pre_2530_);
lean_dec(v_toPure_2524_);
v_getRef_2533_ = lean_ctor_get(v_toMonadRef_2525_, 0);
lean_inc(v_getRef_2533_);
v_withRef_2534_ = lean_ctor_get(v_toMonadRef_2525_, 1);
lean_inc(v_withRef_2534_);
lean_dec_ref(v_toMonadRef_2525_);
lean_inc(v_val_2526_);
v___x_2535_ = lean_apply_1(v_k_2521_, v_val_2526_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2536_, 0, v_stx_2520_);
lean_closure_set(v___f_2536_, 1, v_withRef_2534_);
lean_closure_set(v___f_2536_, 2, v___x_2535_);
v___x_2537_ = lean_apply_4(v_toBind_2523_, lean_box(0), lean_box(0), v_getRef_2533_, v___f_2536_);
return v___x_2537_;
}
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v_k_2521_);
v___x_2538_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2539_ = l_Lean_throwErrorAt___redArg(v_inst_2518_, v_inst_2519_, v_stx_2520_, v___x_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_stx_2543_, lean_object* v_k_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2541_, v_inst_2542_, v_stx_2543_, v_k_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_stx_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc_ref(v_inst_2552_);
lean_inc_ref(v_inst_2546_);
v___x_2554_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2554_, 0, lean_box(0));
lean_closure_set(v___x_2554_, 1, v_inst_2546_);
lean_closure_set(v___x_2554_, 2, v_inst_2547_);
lean_closure_set(v___x_2554_, 3, v_inst_2548_);
lean_closure_set(v___x_2554_, 4, v_inst_2549_);
lean_closure_set(v___x_2554_, 5, v_inst_2550_);
lean_closure_set(v___x_2554_, 6, v_inst_2551_);
lean_closure_set(v___x_2554_, 7, v_inst_2552_);
v___x_2555_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2546_, v_inst_2552_, v_stx_2553_, v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_stx_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_resolveGlobalConst___redArg(v_inst_2557_, v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_inst_2562_, v_inst_2563_, v_stx_2564_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2567_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2568_ = lean_unsigned_to_nat(11u);
v___x_2569_ = lean_unsigned_to_nat(446u);
v___x_2570_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2571_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2572_ = l_mkPanicMessageWithDecl(v___x_2571_, v___x_2570_, v___x_2569_, v___x_2568_, v___x_2567_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_id_2578_, lean_object* v_cs_2579_){
_start:
{
if (lean_obj_tag(v_cs_2579_) == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v_id_2578_);
lean_dec_ref(v_inst_2577_);
v___x_2580_ = lean_box(0);
v___x_2581_ = l_instInhabitedOfMonad___redArg(v_inst_2576_, v___x_2580_);
v___x_2582_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2583_ = l_panic___redArg(v___x_2581_, v___x_2582_);
lean_dec(v___x_2581_);
return v___x_2583_;
}
else
{
lean_object* v_tail_2584_; 
v_tail_2584_ = lean_ctor_get(v_cs_2579_, 1);
if (lean_obj_tag(v_tail_2584_) == 0)
{
lean_object* v_toApplicative_2585_; lean_object* v_toPure_2586_; lean_object* v_head_2587_; lean_object* v___x_2588_; 
v_toApplicative_2585_ = lean_ctor_get(v_inst_2576_, 0);
lean_inc_ref(v_toApplicative_2585_);
lean_dec(v_id_2578_);
lean_dec_ref(v_inst_2577_);
lean_dec_ref(v_inst_2576_);
v_toPure_2586_ = lean_ctor_get(v_toApplicative_2585_, 1);
lean_inc(v_toPure_2586_);
lean_dec_ref(v_toApplicative_2585_);
v_head_2587_ = lean_ctor_get(v_cs_2579_, 0);
lean_inc(v_head_2587_);
lean_dec_ref_known(v_cs_2579_, 2);
v___x_2588_ = lean_apply_2(v_toPure_2586_, lean_box(0), v_head_2587_);
return v___x_2588_;
}
else
{
lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___f_2589_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2590_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2591_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2592_ = lean_box(0);
v___x_2593_ = 0;
lean_inc(v_id_2578_);
v___x_2594_ = l_Lean_Syntax_formatStx(v_id_2578_, v___x_2592_, v___x_2593_);
v___x_2595_ = l_Std_Format_defWidth;
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = l_Std_Format_pretty(v___x_2594_, v___x_2595_, v___x_2596_, v___x_2596_);
v___x_2598_ = lean_string_append(v___x_2591_, v___x_2597_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2600_ = lean_string_append(v___x_2598_, v___x_2599_);
v___x_2601_ = lean_box(0);
v___x_2602_ = l_List_mapTR_loop___redArg(v___f_2589_, v_cs_2579_, v___x_2601_);
v___x_2603_ = l_List_toString___redArg(v___x_2590_, v___x_2602_);
v___x_2604_ = lean_string_append(v___x_2600_, v___x_2603_);
lean_dec_ref(v___x_2603_);
v___x_2605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
v___x_2606_ = l_Lean_MessageData_ofFormat(v___x_2605_);
v___x_2607_ = l_Lean_throwErrorAt___redArg(v_inst_2576_, v_inst_2577_, v_id_2578_, v___x_2606_);
return v___x_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_id_2611_, lean_object* v_cs_2612_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2609_, v_inst_2610_, v_id_2611_, v_cs_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_id_2616_, lean_object* v_____do__lift_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2614_, v_inst_2615_, v_id_2616_, v_____do__lift_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_id_2626_){
_start:
{
lean_object* v_toBind_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_toBind_2627_ = lean_ctor_get(v_inst_2619_, 1);
lean_inc(v_toBind_2627_);
lean_inc(v_id_2626_);
lean_inc_ref(v_inst_2625_);
lean_inc_ref(v_inst_2619_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2628_, 0, v_inst_2619_);
lean_closure_set(v___f_2628_, 1, v_inst_2625_);
lean_closure_set(v___f_2628_, 2, v_id_2626_);
v___x_2629_ = l_Lean_resolveGlobalConst___redArg(v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_inst_2623_, v_inst_2624_, v_inst_2625_, v_id_2626_);
v___x_2630_ = lean_apply_4(v_toBind_2627_, lean_box(0), lean_box(0), v___x_2629_, v___f_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_id_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2632_, v_inst_2633_, v_inst_2634_, v_inst_2635_, v_inst_2636_, v_inst_2637_, v_inst_2638_, v_id_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v_fst_2641_, lean_object* v_snd_2642_, lean_object* v_toPure_2643_, lean_object* v_____r_2644_){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = l_Lean_LocalDecl_toExpr(v_fst_2641_);
v___x_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v_snd_2642_);
v___x_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
v___x_2648_ = lean_apply_2(v_toPure_2643_, lean_box(0), v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_snd_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v_snd_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v_snd_2651_ = lean_ctor_get(v_x_2650_, 1);
v___x_2652_ = l_List_lengthTR___redArg(v_snd_2651_);
v___x_2653_ = l_List_lengthTR___redArg(v_snd_2649_);
v___x_2654_ = lean_nat_dec_lt(v___x_2652_, v___x_2653_);
lean_dec(v___x_2653_);
lean_dec(v___x_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_snd_2655_, lean_object* v_x_2656_){
_start:
{
uint8_t v_res_2657_; lean_object* v_r_2658_; 
v_res_2657_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_snd_2655_, v_x_2656_);
lean_dec_ref(v_x_2656_);
lean_dec(v_snd_2655_);
v_r_2658_ = lean_box(v_res_2657_);
return v_r_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2(lean_object* v___f_2659_, lean_object* v___f_2660_, lean_object* v_toPure_2661_, lean_object* v_r_2662_){
_start:
{
uint8_t v___x_2663_; 
v___x_2663_ = l_List_any___redArg(v_r_2662_, v___f_2659_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec(v_toPure_2661_);
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_apply_1(v___f_2660_, v___x_2664_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec(v___f_2660_);
v___x_2666_ = lean_box(0);
v___x_2667_ = lean_apply_2(v_toPure_2661_, lean_box(0), v___x_2666_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_view_2674_, lean_object* v_findLocalDecl_x3f_2675_, lean_object* v_n_2676_, lean_object* v_projs_2677_, lean_object* v_auxDecl_x3f_2678_){
_start:
{
lean_object* v_toApplicative_2679_; lean_object* v_toBind_2680_; lean_object* v_toPure_2681_; lean_object* v_auxDecl_x3f_2683_; lean_object* v_imported_2702_; lean_object* v_ctx_2703_; lean_object* v_scopes_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_toApplicative_2679_ = lean_ctor_get(v_inst_2668_, 0);
v_toBind_2680_ = lean_ctor_get(v_inst_2668_, 1);
v_toPure_2681_ = lean_ctor_get(v_toApplicative_2679_, 1);
v_imported_2702_ = lean_ctor_get(v_view_2674_, 1);
v_ctx_2703_ = lean_ctor_get(v_view_2674_, 2);
v_scopes_2704_ = lean_ctor_get(v_view_2674_, 3);
lean_inc(v_scopes_2704_);
lean_inc(v_ctx_2703_);
lean_inc(v_imported_2702_);
lean_inc(v_n_2676_);
v___x_2705_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2705_, 0, v_n_2676_);
lean_ctor_set(v___x_2705_, 1, v_imported_2702_);
lean_ctor_set(v___x_2705_, 2, v_ctx_2703_);
lean_ctor_set(v___x_2705_, 3, v_scopes_2704_);
lean_inc_ref(v_findLocalDecl_x3f_2675_);
v___x_2706_ = lean_apply_1(v_findLocalDecl_x3f_2675_, v___x_2705_);
if (lean_obj_tag(v___x_2706_) == 1)
{
lean_object* v_val_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2730_; 
v_val_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2730_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_val_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2730_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
uint8_t v___x_2711_; 
v___x_2711_ = l_Lean_LocalDecl_isAuxDecl(v_val_2707_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2723_; 
lean_inc(v_toPure_2681_);
lean_dec(v_auxDecl_x3f_2678_);
lean_dec(v_n_2676_);
lean_dec_ref(v_findLocalDecl_x3f_2675_);
lean_dec_ref(v_view_2674_);
lean_dec(v_inst_2673_);
lean_dec_ref(v_inst_2672_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec_ref(v_inst_2669_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_inst_2668_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2724_ = lean_ctor_get(v_inst_2668_, 1);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_inst_2668_, 0);
lean_dec(v_unused_2725_);
v___x_2713_ = v_inst_2668_;
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
else
{
lean_dec(v_inst_2668_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = l_Lean_LocalDecl_toExpr(v_val_2707_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 1, v_projs_2677_);
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_projs_2677_);
v___x_2717_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2719_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2717_);
v___x_2719_ = v___x_2709_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_apply_2(v_toPure_2681_, lean_box(0), v___x_2719_);
return v___x_2720_;
}
}
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_2678_) == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_inc(v_projs_2677_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_val_2707_);
lean_ctor_set(v___x_2726_, 1, v_projs_2677_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2726_);
v___x_2728_ = v___x_2709_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
v_auxDecl_x3f_2683_ = v___x_2728_;
goto v___jp_2682_;
}
}
else
{
lean_del_object(v___x_2709_);
lean_dec(v_val_2707_);
v_auxDecl_x3f_2683_ = v_auxDecl_x3f_2678_;
goto v___jp_2682_;
}
}
}
}
else
{
lean_dec(v___x_2706_);
v_auxDecl_x3f_2683_ = v_auxDecl_x3f_2678_;
goto v___jp_2682_;
}
v___jp_2682_:
{
if (lean_obj_tag(v_n_2676_) == 1)
{
lean_object* v_pre_2684_; lean_object* v_str_2685_; lean_object* v___x_2686_; 
v_pre_2684_ = lean_ctor_get(v_n_2676_, 0);
lean_inc(v_pre_2684_);
v_str_2685_ = lean_ctor_get(v_n_2676_, 1);
lean_inc_ref(v_str_2685_);
lean_dec_ref_known(v_n_2676_, 2);
v___x_2686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_str_2685_);
lean_ctor_set(v___x_2686_, 1, v_projs_2677_);
v_n_2676_ = v_pre_2684_;
v_projs_2677_ = v___x_2686_;
v_auxDecl_x3f_2678_ = v_auxDecl_x3f_2683_;
goto _start;
}
else
{
lean_inc(v_toBind_2680_);
lean_dec(v_projs_2677_);
lean_dec(v_n_2676_);
lean_dec_ref(v_findLocalDecl_x3f_2675_);
if (lean_obj_tag(v_auxDecl_x3f_2683_) == 1)
{
lean_object* v_val_2688_; lean_object* v_fst_2689_; lean_object* v_snd_2690_; lean_object* v___f_2691_; uint8_t v___x_2692_; 
v_val_2688_ = lean_ctor_get(v_auxDecl_x3f_2683_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v_auxDecl_x3f_2683_, 1);
v_fst_2689_ = lean_ctor_get(v_val_2688_, 0);
lean_inc_n(v_fst_2689_, 2);
v_snd_2690_ = lean_ctor_get(v_val_2688_, 1);
lean_inc_n(v_snd_2690_, 2);
lean_dec(v_val_2688_);
lean_inc(v_toPure_2681_);
v___f_2691_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2691_, 0, v_fst_2689_);
lean_closure_set(v___f_2691_, 1, v_snd_2690_);
lean_closure_set(v___f_2691_, 2, v_toPure_2681_);
v___x_2692_ = l_List_isEmpty___redArg(v_snd_2690_);
if (v___x_2692_ == 0)
{
lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_dec(v_fst_2689_);
v___f_2693_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2693_, 0, v_snd_2690_);
lean_inc(v_toPure_2681_);
v___f_2694_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2694_, 0, v___f_2693_);
lean_closure_set(v___f_2694_, 1, v___f_2691_);
lean_closure_set(v___f_2694_, 2, v_toPure_2681_);
v___x_2695_ = l_Lean_MacroScopesView_review(v_view_2674_);
v___x_2696_ = l_Lean_resolveGlobalName___redArg(v_inst_2668_, v_inst_2669_, v_inst_2670_, v_inst_2671_, v_inst_2672_, v_inst_2673_, v___x_2695_, v___x_2692_);
v___x_2697_ = lean_apply_4(v_toBind_2680_, lean_box(0), lean_box(0), v___x_2696_, v___f_2694_);
return v___x_2697_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_inc(v_toPure_2681_);
lean_dec_ref(v___f_2691_);
lean_dec(v_toBind_2680_);
lean_dec_ref(v_view_2674_);
lean_dec(v_inst_2673_);
lean_dec_ref(v_inst_2672_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec_ref(v_inst_2669_);
lean_dec_ref(v_inst_2668_);
v___x_2698_ = lean_box(0);
v___x_2699_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v_fst_2689_, v_snd_2690_, v_toPure_2681_, v___x_2698_);
return v___x_2699_;
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_inc(v_toPure_2681_);
lean_dec(v_auxDecl_x3f_2683_);
lean_dec(v_toBind_2680_);
lean_dec_ref(v_view_2674_);
lean_dec(v_inst_2673_);
lean_dec_ref(v_inst_2672_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec_ref(v_inst_2669_);
lean_dec_ref(v_inst_2668_);
v___x_2700_ = lean_box(0);
v___x_2701_ = lean_apply_2(v_toPure_2681_, lean_box(0), v___x_2700_);
return v___x_2701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_view_2738_, lean_object* v_findLocalDecl_x3f_2739_, lean_object* v_n_2740_, lean_object* v_projs_2741_, lean_object* v_auxDecl_x3f_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2732_, v_inst_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_view_2738_, v_findLocalDecl_x3f_2739_, v_n_2740_, v_projs_2741_, v_auxDecl_x3f_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2744_, lean_object* v_givenNameView_2745_, lean_object* v_fullDeclName_2746_, lean_object* v_ns_2747_){
_start:
{
lean_object* v_name_2748_; lean_object* v_imported_2749_; lean_object* v_ctx_2750_; lean_object* v_scopes_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v_name_2748_ = lean_ctor_get(v_givenNameView_2745_, 0);
v_imported_2749_ = lean_ctor_get(v_givenNameView_2745_, 1);
v_ctx_2750_ = lean_ctor_get(v_givenNameView_2745_, 2);
v_scopes_2751_ = lean_ctor_get(v_givenNameView_2745_, 3);
lean_inc(v_name_2748_);
lean_inc(v_ns_2747_);
v___x_2752_ = l_Lean_Name_append(v_ns_2747_, v_name_2748_);
lean_inc(v_scopes_2751_);
lean_inc(v_ctx_2750_);
lean_inc(v_imported_2749_);
v___x_2753_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v_imported_2749_);
lean_ctor_set(v___x_2753_, 2, v_ctx_2750_);
lean_ctor_set(v___x_2753_, 3, v_scopes_2751_);
v___x_2754_ = l_Lean_MacroScopesView_review(v___x_2753_);
v___x_2755_ = lean_name_eq(v___x_2754_, v_fullDeclName_2746_);
lean_dec(v___x_2754_);
if (v___x_2755_ == 0)
{
if (lean_obj_tag(v_ns_2747_) == 1)
{
lean_object* v_pre_2756_; 
v_pre_2756_ = lean_ctor_get(v_ns_2747_, 0);
lean_inc(v_pre_2756_);
lean_dec_ref_known(v_ns_2747_, 2);
v_ns_2747_ = v_pre_2756_;
goto _start;
}
else
{
lean_object* v___x_2758_; 
lean_dec(v_ns_2747_);
lean_dec_ref(v_givenNameView_2745_);
lean_dec_ref(v_localDecl_2744_);
v___x_2758_ = lean_box(0);
return v___x_2758_;
}
}
else
{
lean_object* v___x_2759_; 
lean_dec(v_ns_2747_);
lean_dec_ref(v_givenNameView_2745_);
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_localDecl_2744_);
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2760_, lean_object* v_givenNameView_2761_, lean_object* v_fullDeclName_2762_, lean_object* v_ns_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2760_, v_givenNameView_2761_, v_fullDeclName_2762_, v_ns_2763_);
lean_dec(v_fullDeclName_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2765_, lean_object* v_givenName_2766_){
_start:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = l_Lean_LocalDecl_userName(v_localDecl_2765_);
v___x_2768_ = lean_name_eq(v___x_2767_, v_givenName_2766_);
lean_dec(v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
lean_dec_ref(v_localDecl_2765_);
v___x_2769_ = lean_box(0);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_localDecl_2765_);
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2771_, lean_object* v_givenName_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2771_, v_givenName_2772_);
lean_dec(v_givenName_2772_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2774_, lean_object* v_givenName_2775_, lean_object* v___f_2776_, lean_object* v_auxDeclToFullName_2777_, lean_object* v_currNamespace_2778_, lean_object* v_givenNameView_2779_, lean_object* v_x_2780_){
_start:
{
if (lean_obj_tag(v_x_2780_) == 0)
{
lean_dec_ref(v_givenNameView_2779_);
lean_dec(v_currNamespace_2778_);
lean_dec(v_auxDeclToFullName_2777_);
lean_dec_ref(v___f_2776_);
lean_dec(v_givenName_2775_);
lean_dec_ref(v_matchLocalDecl_x3f_2774_);
return v_x_2780_;
}
else
{
lean_object* v_val_2781_; uint8_t v___x_2782_; 
v_val_2781_ = lean_ctor_get(v_x_2780_, 0);
v___x_2782_ = l_Lean_LocalDecl_isAuxDecl(v_val_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
lean_inc(v_val_2781_);
lean_dec_ref_known(v_x_2780_, 1);
lean_dec_ref(v_givenNameView_2779_);
lean_dec(v_currNamespace_2778_);
lean_dec(v_auxDeclToFullName_2777_);
lean_dec_ref(v___f_2776_);
v___x_2783_ = lean_apply_2(v_matchLocalDecl_x3f_2774_, v_val_2781_, v_givenName_2775_);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = l_Lean_LocalDecl_fvarId(v_val_2781_);
v___x_2785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2776_, v_auxDeclToFullName_2777_, v___x_2784_);
if (lean_obj_tag(v___x_2785_) == 1)
{
lean_object* v_val_2786_; lean_object* v_fullDeclView_2787_; lean_object* v_name_2788_; lean_object* v_imported_2789_; lean_object* v_ctx_2790_; lean_object* v_scopes_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_givenName_2775_);
lean_dec_ref(v_matchLocalDecl_x3f_2774_);
v_val_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v_fullDeclView_2787_ = l_Lean_extractMacroScopes(v_val_2786_);
v_name_2788_ = lean_ctor_get(v_fullDeclView_2787_, 0);
v_imported_2789_ = lean_ctor_get(v_fullDeclView_2787_, 1);
v_ctx_2790_ = lean_ctor_get(v_fullDeclView_2787_, 2);
v_scopes_2791_ = lean_ctor_get(v_fullDeclView_2787_, 3);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_fullDeclView_2787_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2793_ = v_fullDeclView_2787_;
v_isShared_2794_ = v_isSharedCheck_2811_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_scopes_2791_);
lean_inc(v_ctx_2790_);
lean_inc(v_imported_2789_);
lean_inc(v_name_2788_);
lean_dec(v_fullDeclView_2787_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2811_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___y_2796_; lean_object* v___x_2809_; 
lean_inc(v_name_2788_);
v___x_2809_ = l_Lean_privateToUserName_x3f(v_name_2788_);
if (lean_obj_tag(v___x_2809_) == 0)
{
v___y_2796_ = v_name_2788_;
goto v___jp_2795_;
}
else
{
lean_object* v_val_2810_; 
lean_dec(v_name_2788_);
v_val_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___y_2796_ = v_val_2810_;
goto v___jp_2795_;
}
v___jp_2795_:
{
lean_object* v_fullDeclView_2798_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___y_2796_);
v_fullDeclView_2798_ = v___x_2793_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___y_2796_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_imported_2789_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_ctx_2790_);
lean_ctor_set(v_reuseFailAlloc_2808_, 3, v_scopes_2791_);
v_fullDeclView_2798_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v_fullDeclName_2799_; uint8_t v___x_2800_; 
lean_inc_ref(v_fullDeclView_2798_);
v_fullDeclName_2799_ = l_Lean_MacroScopesView_review(v_fullDeclView_2798_);
v___x_2800_ = l_Lean_Name_isPrefixOf(v_currNamespace_2778_, v_fullDeclName_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_inc(v_val_2781_);
lean_dec_ref(v_fullDeclView_2798_);
lean_dec_ref_known(v_x_2780_, 1);
v___x_2801_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2781_, v_givenNameView_2779_, v_fullDeclName_2799_, v_currNamespace_2778_);
lean_dec(v_fullDeclName_2799_);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; lean_object* v_localDeclNameView_2803_; uint8_t v___x_2804_; 
lean_dec(v_fullDeclName_2799_);
lean_dec(v_currNamespace_2778_);
v___x_2802_ = l_Lean_LocalDecl_userName(v_val_2781_);
v_localDeclNameView_2803_ = l_Lean_extractMacroScopes(v___x_2802_);
v___x_2804_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2803_, v_givenNameView_2779_);
lean_dec_ref(v_localDeclNameView_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_dec_ref(v_fullDeclView_2798_);
lean_dec_ref_known(v_x_2780_, 1);
lean_dec_ref(v_givenNameView_2779_);
v___x_2805_ = lean_box(0);
return v___x_2805_;
}
else
{
uint8_t v___x_2806_; 
v___x_2806_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2779_, v_fullDeclView_2798_);
lean_dec_ref(v_fullDeclView_2798_);
lean_dec_ref(v_givenNameView_2779_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
lean_dec_ref_known(v_x_2780_, 1);
v___x_2807_ = lean_box(0);
return v___x_2807_;
}
else
{
return v_x_2780_;
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
lean_inc(v_val_2781_);
lean_dec(v___x_2785_);
lean_dec_ref_known(v_x_2780_, 1);
lean_dec_ref(v_givenNameView_2779_);
lean_dec(v_currNamespace_2778_);
v___x_2812_ = lean_apply_2(v_matchLocalDecl_x3f_2774_, v_val_2781_, v_givenName_2775_);
return v___x_2812_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2844_, lean_object* v_matchLocalDecl_x3f_2845_, lean_object* v___f_2846_, lean_object* v_auxDeclToFullName_2847_, lean_object* v_currNamespace_2848_, lean_object* v_givenNameView_2849_){
_start:
{
lean_object* v_decls_2850_; lean_object* v_givenName_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; lean_object* v_localDecl_x3f_2854_; 
v_decls_2850_ = lean_ctor_get(v_lctx_2844_, 1);
lean_inc_ref_n(v_decls_2850_, 2);
lean_dec_ref(v_lctx_2844_);
lean_inc_ref(v_givenNameView_2849_);
v_givenName_2851_ = l_Lean_MacroScopesView_review(v_givenNameView_2849_);
lean_inc(v_givenName_2851_);
lean_inc_ref(v_matchLocalDecl_x3f_2845_);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2852_, 0, v_matchLocalDecl_x3f_2845_);
lean_closure_set(v___f_2852_, 1, v_givenName_2851_);
lean_closure_set(v___f_2852_, 2, v___f_2846_);
lean_closure_set(v___f_2852_, 3, v_auxDeclToFullName_2847_);
lean_closure_set(v___f_2852_, 4, v_currNamespace_2848_);
lean_closure_set(v___f_2852_, 5, v_givenNameView_2849_);
v___x_2853_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2854_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2853_, v_decls_2850_, v___f_2852_);
if (lean_obj_tag(v_localDecl_x3f_2854_) == 0)
{
lean_object* v___f_2855_; lean_object* v___x_2856_; 
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2855_, 0, v_localDecl_x3f_2854_);
lean_closure_set(v___f_2855_, 1, v_matchLocalDecl_x3f_2845_);
lean_closure_set(v___f_2855_, 2, v_givenName_2851_);
v___x_2856_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2853_, v_decls_2850_, v___f_2855_);
return v___x_2856_;
}
else
{
lean_dec(v_givenName_2851_);
lean_dec_ref(v_decls_2850_);
lean_dec_ref(v_matchLocalDecl_x3f_2845_);
return v_localDecl_x3f_2854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2857_, lean_object* v_lctx_2858_, lean_object* v_matchLocalDecl_x3f_2859_, lean_object* v___f_2860_, lean_object* v_auxDeclToFullName_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_currNamespace_2868_){
_start:
{
lean_object* v_view_2869_; lean_object* v_name_2870_; lean_object* v_findLocalDecl_x3f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_view_2869_ = l_Lean_extractMacroScopes(v_n_2857_);
v_name_2870_ = lean_ctor_get(v_view_2869_, 0);
lean_inc(v_name_2870_);
v_findLocalDecl_x3f_2871_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3), 6, 5);
lean_closure_set(v_findLocalDecl_x3f_2871_, 0, v_lctx_2858_);
lean_closure_set(v_findLocalDecl_x3f_2871_, 1, v_matchLocalDecl_x3f_2859_);
lean_closure_set(v_findLocalDecl_x3f_2871_, 2, v___f_2860_);
lean_closure_set(v_findLocalDecl_x3f_2871_, 3, v_auxDeclToFullName_2861_);
lean_closure_set(v_findLocalDecl_x3f_2871_, 4, v_currNamespace_2868_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_box(0);
v___x_2874_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2862_, v_inst_2863_, v_inst_2864_, v_inst_2865_, v_inst_2866_, v_inst_2867_, v_view_2869_, v_findLocalDecl_x3f_2871_, v_name_2870_, v___x_2872_, v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2875_, lean_object* v_n_2876_, lean_object* v_lctx_2877_, lean_object* v_matchLocalDecl_x3f_2878_, lean_object* v___f_2879_, lean_object* v_inst_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_toBind_2885_, lean_object* v_____do__lift_2886_){
_start:
{
lean_object* v_auxDeclToFullName_2887_; lean_object* v_getCurrNamespace_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; 
v_auxDeclToFullName_2887_ = lean_ctor_get(v_____do__lift_2886_, 2);
lean_inc(v_auxDeclToFullName_2887_);
lean_dec_ref(v_____do__lift_2886_);
v_getCurrNamespace_2888_ = lean_ctor_get(v_inst_2875_, 0);
lean_inc(v_getCurrNamespace_2888_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2889_, 0, v_n_2876_);
lean_closure_set(v___f_2889_, 1, v_lctx_2877_);
lean_closure_set(v___f_2889_, 2, v_matchLocalDecl_x3f_2878_);
lean_closure_set(v___f_2889_, 3, v___f_2879_);
lean_closure_set(v___f_2889_, 4, v_auxDeclToFullName_2887_);
lean_closure_set(v___f_2889_, 5, v_inst_2880_);
lean_closure_set(v___f_2889_, 6, v_inst_2875_);
lean_closure_set(v___f_2889_, 7, v_inst_2881_);
lean_closure_set(v___f_2889_, 8, v_inst_2882_);
lean_closure_set(v___f_2889_, 9, v_inst_2883_);
lean_closure_set(v___f_2889_, 10, v_inst_2884_);
v___x_2890_ = lean_apply_4(v_toBind_2885_, lean_box(0), lean_box(0), v_getCurrNamespace_2888_, v___f_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2891_, lean_object* v_n_2892_, lean_object* v_matchLocalDecl_x3f_2893_, lean_object* v___f_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_toBind_2900_, lean_object* v_inst_2901_, lean_object* v_lctx_2902_){
_start:
{
lean_object* v___f_2903_; lean_object* v___x_2904_; 
lean_inc(v_toBind_2900_);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2903_, 0, v_inst_2891_);
lean_closure_set(v___f_2903_, 1, v_n_2892_);
lean_closure_set(v___f_2903_, 2, v_lctx_2902_);
lean_closure_set(v___f_2903_, 3, v_matchLocalDecl_x3f_2893_);
lean_closure_set(v___f_2903_, 4, v___f_2894_);
lean_closure_set(v___f_2903_, 5, v_inst_2895_);
lean_closure_set(v___f_2903_, 6, v_inst_2896_);
lean_closure_set(v___f_2903_, 7, v_inst_2897_);
lean_closure_set(v___f_2903_, 8, v_inst_2898_);
lean_closure_set(v___f_2903_, 9, v_inst_2899_);
lean_closure_set(v___f_2903_, 10, v_toBind_2900_);
v___x_2904_ = lean_apply_4(v_toBind_2900_, lean_box(0), lean_box(0), v_inst_2901_, v___f_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_n_2914_){
_start:
{
lean_object* v_toBind_2915_; lean_object* v___f_2916_; lean_object* v_matchLocalDecl_x3f_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; 
v_toBind_2915_ = lean_ctor_get(v_inst_2907_, 1);
lean_inc_n(v_toBind_2915_, 2);
v___f_2916_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2917_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2913_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2918_, 0, v_inst_2908_);
lean_closure_set(v___f_2918_, 1, v_n_2914_);
lean_closure_set(v___f_2918_, 2, v_matchLocalDecl_x3f_2917_);
lean_closure_set(v___f_2918_, 3, v___f_2916_);
lean_closure_set(v___f_2918_, 4, v_inst_2907_);
lean_closure_set(v___f_2918_, 5, v_inst_2909_);
lean_closure_set(v___f_2918_, 6, v_inst_2910_);
lean_closure_set(v___f_2918_, 7, v_inst_2911_);
lean_closure_set(v___f_2918_, 8, v_inst_2912_);
lean_closure_set(v___f_2918_, 9, v_toBind_2915_);
lean_closure_set(v___f_2918_, 10, v_inst_2913_);
v___x_2919_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v_inst_2913_, v___f_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_n_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_resolveLocalName___redArg(v_inst_2921_, v_inst_2922_, v_inst_2923_, v_inst_2924_, v_inst_2925_, v_inst_2926_, v_inst_2927_, v_n_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2930_, uint8_t v_____do__lift_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_box(v_____do__lift_2931_);
v___x_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
v___x_2934_ = lean_apply_2(v_toPure_2930_, lean_box(0), v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2935_, lean_object* v_____do__lift_2936_){
_start:
{
uint8_t v_____do__lift_1060__boxed_2937_; lean_object* v_res_2938_; 
v_____do__lift_1060__boxed_2937_ = lean_unbox(v_____do__lift_2936_);
v_res_2938_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2935_, v_____do__lift_1060__boxed_2937_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2939_, lean_object* v___y_2940_, lean_object* v_____do__lift_2941_){
_start:
{
if (lean_obj_tag(v_____do__lift_2941_) == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_dec(v___y_2940_);
v___x_2942_ = lean_box(0);
v___x_2943_ = lean_apply_2(v_toPure_2939_, lean_box(0), v___x_2942_);
return v___x_2943_;
}
else
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2951_; 
v_isSharedCheck_2951_ = !lean_is_exclusive(v_____do__lift_2941_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v_____do__lift_2941_, 0);
lean_dec(v_unused_2952_);
v___x_2945_ = v_____do__lift_2941_;
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v_____do__lift_2941_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___y_2940_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___y_2940_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_apply_2(v_toPure_2939_, lean_box(0), v___x_2948_);
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2955_, lean_object* v_toBind_2956_, lean_object* v___f_2957_, lean_object* v_____do__lift_2958_){
_start:
{
if (lean_obj_tag(v_____do__lift_2958_) == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v___f_2957_);
lean_dec(v_toBind_2956_);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_apply_2(v_toPure_2955_, lean_box(0), v___x_2959_);
return v___x_2960_;
}
else
{
lean_object* v_val_2961_; uint8_t v___x_2962_; 
v_val_2961_ = lean_ctor_get(v_____do__lift_2958_, 0);
v___x_2962_ = lean_unbox(v_val_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_apply_2(v_toPure_2955_, lean_box(0), v___x_2963_);
v___x_2965_ = lean_apply_4(v_toBind_2956_, lean_box(0), lean_box(0), v___x_2964_, v___f_2957_);
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2967_ = lean_apply_2(v_toPure_2955_, lean_box(0), v___x_2966_);
v___x_2968_ = lean_apply_4(v_toBind_2956_, lean_box(0), lean_box(0), v___x_2967_, v___f_2957_);
return v___x_2968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2969_, lean_object* v_toBind_2970_, lean_object* v___f_2971_, lean_object* v_____do__lift_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2969_, v_toBind_2970_, v___f_2971_, v_____do__lift_2972_);
lean_dec(v_____do__lift_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2974_, lean_object* v_filter_2975_, lean_object* v___y_2976_, lean_object* v_toBind_2977_, lean_object* v___f_2978_, lean_object* v___f_2979_, lean_object* v_____do__lift_2980_){
_start:
{
if (lean_obj_tag(v_____do__lift_2980_) == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec(v___f_2979_);
lean_dec(v___f_2978_);
lean_dec(v_toBind_2977_);
lean_dec(v___y_2976_);
lean_dec(v_filter_2975_);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_apply_2(v_toPure_2974_, lean_box(0), v___x_2981_);
return v___x_2982_;
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec(v_toPure_2974_);
v___x_2983_ = lean_apply_1(v_filter_2975_, v___y_2976_);
lean_inc(v_toBind_2977_);
v___x_2984_ = lean_apply_4(v_toBind_2977_, lean_box(0), lean_box(0), v___x_2983_, v___f_2978_);
v___x_2985_ = lean_apply_4(v_toBind_2977_, lean_box(0), lean_box(0), v___x_2984_, v___f_2979_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_2986_, lean_object* v_filter_2987_, lean_object* v___y_2988_, lean_object* v_toBind_2989_, lean_object* v___f_2990_, lean_object* v___f_2991_, lean_object* v_____do__lift_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_2986_, v_filter_2987_, v___y_2988_, v_toBind_2989_, v___f_2990_, v___f_2991_, v_____do__lift_2992_);
lean_dec(v_____do__lift_2992_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_2994_, lean_object* v_n_u2080_2995_, lean_object* v_toBind_2996_, lean_object* v___f_2997_, lean_object* v_____do__lift_2998_){
_start:
{
if (lean_obj_tag(v_____do__lift_2998_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec(v___f_2997_);
lean_dec(v_toBind_2996_);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_apply_2(v_toPure_2994_, lean_box(0), v___x_3002_);
return v___x_3003_;
}
else
{
lean_object* v_val_3004_; 
v_val_3004_ = lean_ctor_get(v_____do__lift_2998_, 0);
if (lean_obj_tag(v_val_3004_) == 1)
{
lean_object* v_tail_3005_; 
v_tail_3005_ = lean_ctor_get(v_val_3004_, 1);
if (lean_obj_tag(v_tail_3005_) == 0)
{
lean_object* v_head_3006_; lean_object* v_fst_3007_; uint8_t v___x_3008_; 
v_head_3006_ = lean_ctor_get(v_val_3004_, 0);
v_fst_3007_ = lean_ctor_get(v_head_3006_, 0);
v___x_3008_ = lean_name_eq(v_fst_3007_, v_n_u2080_2995_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_apply_2(v_toPure_2994_, lean_box(0), v___x_3009_);
v___x_3011_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3010_, v___f_2997_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3013_ = lean_apply_2(v_toPure_2994_, lean_box(0), v___x_3012_);
v___x_3014_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3013_, v___f_2997_);
return v___x_3014_;
}
}
else
{
lean_dec(v___f_2997_);
lean_dec(v_toBind_2996_);
goto v___jp_2999_;
}
}
else
{
lean_dec(v___f_2997_);
lean_dec(v_toBind_2996_);
goto v___jp_2999_;
}
}
v___jp_2999_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_apply_2(v_toPure_2994_, lean_box(0), v___x_3000_);
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3015_, lean_object* v_n_u2080_3016_, lean_object* v_toBind_3017_, lean_object* v___f_3018_, lean_object* v_____do__lift_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3015_, v_n_u2080_3016_, v_toBind_3017_, v___f_3018_, v_____do__lift_3019_);
lean_dec(v_____do__lift_3019_);
lean_dec(v_n_u2080_3016_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_n_u2080_3027_, lean_object* v_filter_3028_, lean_object* v_view_x3f_3029_, lean_object* v_n_3030_){
_start:
{
lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___f_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v_toApplicative_3043_; lean_object* v_getEnv_3044_; lean_object* v_modifyEnv_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3083_; 
lean_inc_ref_n(v_inst_3021_, 8);
v___f_3031_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3031_, 0, v_inst_3021_);
v___f_3032_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3032_, 0, v_inst_3021_);
v___f_3033_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3033_, 0, v_inst_3021_);
v___f_3034_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3034_, 0, v_inst_3021_);
v___f_3035_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3035_, 0, v_inst_3021_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___f_3031_);
lean_ctor_set(v___x_3036_, 1, v___f_3032_);
v___x_3037_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3037_, 0, lean_box(0));
lean_closure_set(v___x_3037_, 1, v_inst_3021_);
v___x_3038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
lean_ctor_set(v___x_3038_, 2, v___f_3033_);
lean_ctor_set(v___x_3038_, 3, v___f_3034_);
lean_ctor_set(v___x_3038_, 4, v___f_3035_);
v___x_3039_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3039_, 0, lean_box(0));
lean_closure_set(v___x_3039_, 1, v_inst_3021_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3041_, 0, lean_box(0));
lean_closure_set(v___x_3041_, 1, v_inst_3021_);
lean_inc_ref(v___x_3041_);
v___x_3042_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3041_, v_inst_3022_);
v_toApplicative_3043_ = lean_ctor_get(v_inst_3021_, 0);
lean_inc_ref(v_toApplicative_3043_);
v_getEnv_3044_ = lean_ctor_get(v_inst_3023_, 0);
v_modifyEnv_3045_ = lean_ctor_get(v_inst_3023_, 1);
v_isSharedCheck_3083_ = !lean_is_exclusive(v_inst_3023_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3047_ = v_inst_3023_;
v_isShared_3048_ = v_isSharedCheck_3083_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_modifyEnv_3045_);
lean_inc(v_getEnv_3044_);
lean_dec(v_inst_3023_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3083_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_toBind_3049_; lean_object* v_toPure_3050_; lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v_toBind_3049_ = lean_ctor_get(v_inst_3021_, 1);
lean_inc_n(v_toBind_3049_, 2);
lean_dec_ref(v_inst_3021_);
v_toPure_3050_ = lean_ctor_get(v_toApplicative_3043_, 1);
lean_inc_n(v_toPure_3050_, 3);
lean_dec_ref(v_toApplicative_3043_);
lean_inc_ref(v___x_3041_);
v___f_3051_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3051_, 0, v_modifyEnv_3045_);
lean_closure_set(v___f_3051_, 1, v___x_3041_);
v___f_3052_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3052_, 0, v_toPure_3050_);
v___f_3053_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3053_, 0, v_toPure_3050_);
v___x_3054_ = lean_apply_4(v_toBind_3049_, lean_box(0), lean_box(0), v_getEnv_3044_, v___f_3053_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___f_3051_);
lean_ctor_set(v___x_3047_, 0, v___x_3054_);
v___x_3056_ = v___x_3047_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v___f_3051_);
v___x_3056_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___f_3059_; lean_object* v___y_3061_; 
lean_inc_ref_n(v___x_3041_, 2);
v___x_3057_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_3041_, v_inst_3024_);
v___x_3058_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3041_, v_inst_3025_);
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3059_, 0, v_inst_3026_);
lean_closure_set(v___f_3059_, 1, v___x_3041_);
if (lean_obj_tag(v_view_x3f_3029_) == 1)
{
lean_object* v_val_3069_; lean_object* v_imported_3070_; lean_object* v_ctx_3071_; lean_object* v_scopes_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3080_; 
v_val_3069_ = lean_ctor_get(v_view_x3f_3029_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v_view_x3f_3029_, 1);
v_imported_3070_ = lean_ctor_get(v_val_3069_, 1);
v_ctx_3071_ = lean_ctor_get(v_val_3069_, 2);
v_scopes_3072_ = lean_ctor_get(v_val_3069_, 3);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_val_3069_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v_val_3069_, 0);
lean_dec(v_unused_3081_);
v___x_3074_ = v_val_3069_;
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_scopes_3072_);
lean_inc(v_ctx_3071_);
lean_inc(v_imported_3070_);
lean_dec(v_val_3069_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v_n_3030_);
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_n_3030_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_imported_3070_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_ctx_3071_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_scopes_3072_);
v___x_3077_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_MacroScopesView_review(v___x_3077_);
v___y_3061_ = v___x_3078_;
goto v___jp_3060_;
}
}
}
else
{
lean_dec(v_view_x3f_3029_);
v___y_3061_ = v_n_3030_;
goto v___jp_3060_;
}
v___jp_3060_:
{
lean_object* v___f_3062_; lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_inc_n(v___y_3061_, 2);
lean_inc_n(v_toPure_3050_, 3);
v___f_3062_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3062_, 0, v_toPure_3050_);
lean_closure_set(v___f_3062_, 1, v___y_3061_);
lean_inc_n(v_toBind_3049_, 3);
v___f_3063_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3063_, 0, v_toPure_3050_);
lean_closure_set(v___f_3063_, 1, v_toBind_3049_);
lean_closure_set(v___f_3063_, 2, v___f_3062_);
v___f_3064_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3064_, 0, v_toPure_3050_);
lean_closure_set(v___f_3064_, 1, v_filter_3028_);
lean_closure_set(v___f_3064_, 2, v___y_3061_);
lean_closure_set(v___f_3064_, 3, v_toBind_3049_);
lean_closure_set(v___f_3064_, 4, v___f_3052_);
lean_closure_set(v___f_3064_, 5, v___f_3063_);
v___f_3065_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3065_, 0, v_toPure_3050_);
lean_closure_set(v___f_3065_, 1, v_n_u2080_3027_);
lean_closure_set(v___f_3065_, 2, v_toBind_3049_);
lean_closure_set(v___f_3065_, 3, v___f_3064_);
v___x_3066_ = 0;
v___x_3067_ = l_Lean_resolveGlobalName___redArg(v___x_3040_, v___x_3042_, v___x_3056_, v___x_3057_, v___x_3058_, v___f_3059_, v___y_3061_, v___x_3066_);
v___x_3068_ = lean_apply_4(v_toBind_3049_, lean_box(0), lean_box(0), v___x_3067_, v___f_3065_);
return v___x_3068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_inst_3090_, lean_object* v_n_u2080_3091_, lean_object* v_filter_3092_, lean_object* v_view_x3f_3093_, lean_object* v_n_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3085_, v_inst_3086_, v_inst_3087_, v_inst_3088_, v_inst_3089_, v_inst_3090_, v_n_u2080_3091_, v_filter_3092_, v_view_x3f_3093_, v_n_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3100_, lean_object* v_____x_3101_){
_start:
{
if (lean_obj_tag(v_____x_3101_) == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3103_ = lean_apply_2(v_toPure_3100_, lean_box(0), v___x_3102_);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_apply_2(v_toPure_3100_, lean_box(0), v_____x_3101_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3105_, lean_object* v_____do__lift_3106_){
_start:
{
if (lean_obj_tag(v_____do__lift_3106_) == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_box(0);
v___x_3108_ = lean_apply_2(v_toPure_3105_, lean_box(0), v___x_3107_);
return v___x_3108_;
}
else
{
lean_object* v_val_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3118_; 
v_val_3109_ = lean_ctor_get(v_____do__lift_3106_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_____do__lift_3106_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3111_ = v_____do__lift_3106_;
v_isShared_3112_ = v_isSharedCheck_3118_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_val_3109_);
lean_dec(v_____do__lift_3106_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3118_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_val_3109_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3113_);
v___x_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_apply_2(v_toPure_3105_, lean_box(0), v___x_3115_);
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3119_, lean_object* v___x_3120_, lean_object* v_____do__lift_3121_){
_start:
{
if (lean_obj_tag(v_____do__lift_3121_) == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_apply_2(v_toPure_3119_, lean_box(0), v___x_3120_);
return v___x_3122_;
}
else
{
lean_object* v_val_3123_; lean_object* v_fst_3124_; lean_object* v___x_3125_; 
lean_dec(v___x_3120_);
v_val_3123_ = lean_ctor_get(v_____do__lift_3121_, 0);
lean_inc(v_val_3123_);
lean_dec_ref_known(v_____do__lift_3121_, 1);
v_fst_3124_ = lean_ctor_get(v_val_3123_, 0);
lean_inc(v_fst_3124_);
lean_dec(v_val_3123_);
v___x_3125_ = lean_apply_2(v_toPure_3119_, lean_box(0), v_fst_3124_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3126_, lean_object* v___x_3127_, lean_object* v___x_3128_, lean_object* v_____do__lift_3129_){
_start:
{
if (lean_obj_tag(v_____do__lift_3129_) == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v___x_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v___x_3131_ = lean_apply_2(v_toPure_3126_, lean_box(0), v___x_3130_);
return v___x_3131_;
}
else
{
lean_object* v_val_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3163_; 
v_val_3132_ = lean_ctor_get(v_____do__lift_3129_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_____do__lift_3129_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3134_ = v_____do__lift_3129_;
v_isShared_3135_ = v_isSharedCheck_3163_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_val_3132_);
lean_dec(v_____do__lift_3129_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3163_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
if (lean_obj_tag(v_val_3132_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v___x_3128_);
v_a_3136_ = lean_ctor_get(v_val_3132_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_val_3132_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3138_ = v_val_3132_;
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v_val_3132_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_a_3136_);
v___x_3141_ = v___x_3134_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
lean_ctor_set(v___x_3142_, 1, v___x_3127_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3142_);
v___x_3144_ = v___x_3138_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
v___x_3146_ = lean_apply_2(v_toPure_3126_, lean_box(0), v___x_3145_);
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3161_; 
v_isSharedCheck_3161_ = !lean_is_exclusive(v_val_3132_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v_val_3132_, 0);
lean_dec(v_unused_3162_);
v___x_3151_ = v_val_3132_;
v_isShared_3152_ = v_isSharedCheck_3161_;
goto v_resetjp_3150_;
}
else
{
lean_dec(v_val_3132_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3161_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3128_);
lean_ctor_set(v___x_3153_, 1, v___x_3127_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3155_);
v___x_3157_ = v___x_3134_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_apply_2(v_toPure_3126_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3164_, lean_object* v___x_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_n_u2080_3172_, lean_object* v_filter_3173_, lean_object* v_view_x3f_3174_, lean_object* v_toBind_3175_, lean_object* v___f_3176_, lean_object* v___f_3177_, lean_object* v_a_3178_, lean_object* v_x_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_snd_3181_; lean_object* v___x_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_snd_3181_ = lean_ctor_get(v___y_3180_, 1);
lean_inc(v_snd_3181_);
lean_dec_ref(v___y_3180_);
v___x_3182_ = l_Lean_Name_appendCore(v_a_3178_, v_snd_3181_);
lean_inc(v___x_3182_);
v___f_3183_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3183_, 0, v_toPure_3164_);
lean_closure_set(v___f_3183_, 1, v___x_3182_);
lean_closure_set(v___f_3183_, 2, v___x_3165_);
v___x_3184_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3166_, v_inst_3167_, v_inst_3168_, v_inst_3169_, v_inst_3170_, v_inst_3171_, v_n_u2080_3172_, v_filter_3173_, v_view_x3f_3174_, v___x_3182_);
lean_inc_n(v_toBind_3175_, 2);
v___x_3185_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v___x_3184_, v___f_3176_);
v___x_3186_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v___x_3185_, v___f_3177_);
v___x_3187_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v___x_3186_, v___f_3183_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3188_ = _args[0];
lean_object* v___x_3189_ = _args[1];
lean_object* v_inst_3190_ = _args[2];
lean_object* v_inst_3191_ = _args[3];
lean_object* v_inst_3192_ = _args[4];
lean_object* v_inst_3193_ = _args[5];
lean_object* v_inst_3194_ = _args[6];
lean_object* v_inst_3195_ = _args[7];
lean_object* v_n_u2080_3196_ = _args[8];
lean_object* v_filter_3197_ = _args[9];
lean_object* v_view_x3f_3198_ = _args[10];
lean_object* v_toBind_3199_ = _args[11];
lean_object* v___f_3200_ = _args[12];
lean_object* v___f_3201_ = _args[13];
lean_object* v_a_3202_ = _args[14];
lean_object* v_x_3203_ = _args[15];
lean_object* v___y_3204_ = _args[16];
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3188_, v___x_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_inst_3193_, v_inst_3194_, v_inst_3195_, v_n_u2080_3196_, v_filter_3197_, v_view_x3f_3198_, v_toBind_3199_, v___f_3200_, v___f_3201_, v_a_3202_, v_x_3203_, v___y_3204_);
lean_dec(v_a_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3209_, lean_object* v_n_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_n_u2080_3217_, lean_object* v_filter_3218_, lean_object* v_view_x3f_3219_, lean_object* v_toBind_3220_, lean_object* v___f_3221_, lean_object* v___f_3222_, lean_object* v___x_3223_, lean_object* v_____do__lift_3224_){
_start:
{
if (lean_obj_tag(v_____do__lift_3224_) == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec_ref(v___x_3223_);
lean_dec(v___f_3222_);
lean_dec(v___f_3221_);
lean_dec(v_toBind_3220_);
lean_dec(v_view_x3f_3219_);
lean_dec(v_filter_3218_);
lean_dec(v_n_u2080_3217_);
lean_dec(v_inst_3216_);
lean_dec_ref(v_inst_3215_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_inst_3213_);
lean_dec_ref(v_inst_3212_);
lean_dec_ref(v_inst_3211_);
lean_dec(v_n_3210_);
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_apply_2(v_toPure_3209_, lean_box(0), v___x_3225_);
return v___x_3226_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3227_ = l_Lean_privateToUserName(v_n_3210_);
v___x_3228_ = l_Lean_Name_componentsRev(v___x_3227_);
v___x_3229_ = lean_box(0);
lean_inc(v_toPure_3209_);
v___f_3230_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3230_, 0, v_toPure_3209_);
lean_closure_set(v___f_3230_, 1, v___x_3229_);
lean_inc(v_toBind_3220_);
v___f_3231_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3231_, 0, v_toPure_3209_);
lean_closure_set(v___f_3231_, 1, v___x_3229_);
lean_closure_set(v___f_3231_, 2, v_inst_3211_);
lean_closure_set(v___f_3231_, 3, v_inst_3212_);
lean_closure_set(v___f_3231_, 4, v_inst_3213_);
lean_closure_set(v___f_3231_, 5, v_inst_3214_);
lean_closure_set(v___f_3231_, 6, v_inst_3215_);
lean_closure_set(v___f_3231_, 7, v_inst_3216_);
lean_closure_set(v___f_3231_, 8, v_n_u2080_3217_);
lean_closure_set(v___f_3231_, 9, v_filter_3218_);
lean_closure_set(v___f_3231_, 10, v_view_x3f_3219_);
lean_closure_set(v___f_3231_, 11, v_toBind_3220_);
lean_closure_set(v___f_3231_, 12, v___f_3221_);
lean_closure_set(v___f_3231_, 13, v___f_3222_);
v___x_3232_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3233_ = l_List_forIn_x27_loop___redArg(v___x_3223_, v___f_3231_, v___x_3228_, v___x_3232_);
lean_dec(v___x_3228_);
v___x_3234_ = lean_apply_4(v_toBind_3220_, lean_box(0), lean_box(0), v___x_3233_, v___f_3230_);
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3235_, lean_object* v_n_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_inst_3242_, lean_object* v_n_u2080_3243_, lean_object* v_filter_3244_, lean_object* v_view_x3f_3245_, lean_object* v_toBind_3246_, lean_object* v___f_3247_, lean_object* v___f_3248_, lean_object* v___x_3249_, lean_object* v_____do__lift_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3235_, v_n_3236_, v_inst_3237_, v_inst_3238_, v_inst_3239_, v_inst_3240_, v_inst_3241_, v_inst_3242_, v_n_u2080_3243_, v_filter_3244_, v_view_x3f_3245_, v_toBind_3246_, v___f_3247_, v___f_3248_, v___x_3249_, v_____do__lift_3250_);
lean_dec(v_____do__lift_3250_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_n_u2080_3258_, lean_object* v_filter_3259_, lean_object* v_view_x3f_3260_, lean_object* v_n_3261_){
_start:
{
lean_object* v___f_3262_; lean_object* v___f_3263_; lean_object* v___f_3264_; lean_object* v___f_3265_; lean_object* v___f_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___y_3273_; uint8_t v___x_3281_; 
lean_inc_ref_n(v_inst_3252_, 7);
v___f_3262_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3262_, 0, v_inst_3252_);
v___f_3263_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3263_, 0, v_inst_3252_);
v___f_3264_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3264_, 0, v_inst_3252_);
v___f_3265_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3265_, 0, v_inst_3252_);
v___f_3266_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3266_, 0, v_inst_3252_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___f_3262_);
lean_ctor_set(v___x_3267_, 1, v___f_3263_);
v___x_3268_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3268_, 0, lean_box(0));
lean_closure_set(v___x_3268_, 1, v_inst_3252_);
v___x_3269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
lean_ctor_set(v___x_3269_, 2, v___f_3264_);
lean_ctor_set(v___x_3269_, 3, v___f_3265_);
lean_ctor_set(v___x_3269_, 4, v___f_3266_);
v___x_3270_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3270_, 0, lean_box(0));
lean_closure_set(v___x_3270_, 1, v_inst_3252_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3281_ = l_Lean_Name_hasMacroScopes(v_n_3261_);
if (v___x_3281_ == 0)
{
lean_object* v_toApplicative_3282_; lean_object* v_toPure_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_toApplicative_3282_ = lean_ctor_get(v_inst_3252_, 0);
v_toPure_3283_ = lean_ctor_get(v_toApplicative_3282_, 1);
v___x_3284_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3283_);
v___x_3285_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3284_);
v___y_3273_ = v___x_3285_;
goto v___jp_3272_;
}
else
{
lean_object* v_toApplicative_3286_; lean_object* v_toPure_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_toApplicative_3286_ = lean_ctor_get(v_inst_3252_, 0);
v_toPure_3287_ = lean_ctor_get(v_toApplicative_3286_, 1);
v___x_3288_ = lean_box(0);
lean_inc(v_toPure_3287_);
v___x_3289_ = lean_apply_2(v_toPure_3287_, lean_box(0), v___x_3288_);
v___y_3273_ = v___x_3289_;
goto v___jp_3272_;
}
v___jp_3272_:
{
lean_object* v_toApplicative_3274_; lean_object* v_toBind_3275_; lean_object* v_toPure_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; 
v_toApplicative_3274_ = lean_ctor_get(v_inst_3252_, 0);
v_toBind_3275_ = lean_ctor_get(v_inst_3252_, 1);
lean_inc_n(v_toBind_3275_, 2);
v_toPure_3276_ = lean_ctor_get(v_toApplicative_3274_, 1);
lean_inc_n(v_toPure_3276_, 3);
v___f_3277_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3277_, 0, v_toPure_3276_);
v___f_3278_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3278_, 0, v_toPure_3276_);
v___f_3279_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3279_, 0, v_toPure_3276_);
lean_closure_set(v___f_3279_, 1, v_n_3261_);
lean_closure_set(v___f_3279_, 2, v_inst_3252_);
lean_closure_set(v___f_3279_, 3, v_inst_3253_);
lean_closure_set(v___f_3279_, 4, v_inst_3254_);
lean_closure_set(v___f_3279_, 5, v_inst_3255_);
lean_closure_set(v___f_3279_, 6, v_inst_3256_);
lean_closure_set(v___f_3279_, 7, v_inst_3257_);
lean_closure_set(v___f_3279_, 8, v_n_u2080_3258_);
lean_closure_set(v___f_3279_, 9, v_filter_3259_);
lean_closure_set(v___f_3279_, 10, v_view_x3f_3260_);
lean_closure_set(v___f_3279_, 11, v_toBind_3275_);
lean_closure_set(v___f_3279_, 12, v___f_3278_);
lean_closure_set(v___f_3279_, 13, v___f_3277_);
lean_closure_set(v___f_3279_, 14, v___x_3271_);
v___x_3280_ = lean_apply_4(v_toBind_3275_, lean_box(0), lean_box(0), v___y_3273_, v___f_3279_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_inst_3294_, lean_object* v_inst_3295_, lean_object* v_inst_3296_, lean_object* v_n_u2080_3297_, lean_object* v_filter_3298_, lean_object* v_view_x3f_3299_, lean_object* v_n_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3291_, v_inst_3292_, v_inst_3293_, v_inst_3294_, v_inst_3295_, v_inst_3296_, v_n_u2080_3297_, v_filter_3298_, v_view_x3f_3299_, v_n_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3302_, lean_object* v_x1_3303_, lean_object* v_x2_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3305_ = l_Lean_Name_getPrefix(v_x2_3304_);
v___x_3306_ = l_Lean_Name_getPrefix(v_n_u2081_3302_);
v___x_3307_ = l_Lean_Name_isPrefixOf(v___x_3305_, v___x_3306_);
lean_dec(v___x_3306_);
lean_dec(v___x_3305_);
if (v___x_3307_ == 0)
{
lean_dec(v_x2_3304_);
return v_x1_3303_;
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_array_push(v_x1_3303_, v_x2_3304_);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3309_, lean_object* v_x1_3310_, lean_object* v_x2_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3309_, v_x1_3310_, v_x2_3311_);
lean_dec(v_n_u2081_3309_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3313_, lean_object* v_n_u2081_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_n_u2080_3321_, lean_object* v_filter_3322_, lean_object* v_toPure_3323_, lean_object* v_____do__lift_3324_){
_start:
{
if (lean_obj_tag(v_____do__lift_3324_) == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v_toPure_3323_);
v___x_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_view_3313_);
v___x_3326_ = l_Lean_rootNamespace;
v___x_3327_ = l_Lean_Name_append(v___x_3326_, v_n_u2081_3314_);
v___x_3328_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3315_, v_inst_3316_, v_inst_3317_, v_inst_3318_, v_inst_3319_, v_inst_3320_, v_n_u2080_3321_, v_filter_3322_, v___x_3325_, v___x_3327_);
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; 
lean_dec(v_filter_3322_);
lean_dec(v_n_u2080_3321_);
lean_dec(v_inst_3320_);
lean_dec_ref(v_inst_3319_);
lean_dec_ref(v_inst_3318_);
lean_dec_ref(v_inst_3317_);
lean_dec_ref(v_inst_3316_);
lean_dec_ref(v_inst_3315_);
lean_dec(v_n_u2081_3314_);
lean_dec_ref(v_view_3313_);
v___x_3329_ = lean_apply_2(v_toPure_3323_, lean_box(0), v_____do__lift_3324_);
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_n_u2080_3337_, lean_object* v_filter_3338_, lean_object* v___x_3339_, lean_object* v_toBind_3340_, lean_object* v___f_3341_, uint8_t v_allowHorizAliases_3342_, lean_object* v___f_3343_, lean_object* v_____do__lift_3344_){
_start:
{
lean_object* v_aliases_3346_; 
if (lean_obj_tag(v_____do__lift_3344_) == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v___f_3343_);
lean_dec(v___f_3341_);
lean_dec(v_toBind_3340_);
lean_dec_ref(v___x_3339_);
lean_dec(v_filter_3338_);
lean_dec(v_n_u2080_3337_);
lean_dec(v_inst_3336_);
lean_dec_ref(v_inst_3335_);
lean_dec_ref(v_inst_3334_);
lean_dec_ref(v_inst_3333_);
lean_dec_ref(v_inst_3332_);
lean_dec_ref(v_inst_3331_);
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_apply_2(v_toPure_3330_, lean_box(0), v___x_3352_);
return v___x_3353_;
}
else
{
lean_object* v_val_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec(v_toPure_3330_);
v_val_3354_ = lean_ctor_get(v_____do__lift_3344_, 0);
lean_inc(v_val_3354_);
lean_dec_ref_known(v_____do__lift_3344_, 1);
lean_inc(v_n_u2080_3337_);
v___x_3355_ = l_Lean_getRevAliases(v_val_3354_, v_n_u2080_3337_);
v___x_3356_ = lean_array_mk(v___x_3355_);
if (v_allowHorizAliases_3342_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = lean_array_get_size(v___x_3356_);
v___x_3359_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3360_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3361_ = lean_nat_dec_lt(v___x_3357_, v___x_3358_);
if (v___x_3361_ == 0)
{
lean_dec_ref(v___x_3356_);
lean_dec_ref(v___f_3343_);
v_aliases_3346_ = v___x_3359_;
goto v___jp_3345_;
}
else
{
size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = lean_usize_of_nat(v___x_3358_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3360_, v___f_3343_, v___x_3356_, v___x_3362_, v___x_3363_, v___x_3359_);
v_aliases_3346_ = v___x_3364_;
goto v___jp_3345_;
}
}
else
{
lean_dec_ref(v___f_3343_);
v_aliases_3346_ = v___x_3356_;
goto v___jp_3345_;
}
}
v___jp_3345_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3348_, 0, lean_box(0));
lean_closure_set(v___x_3348_, 1, v_inst_3331_);
lean_closure_set(v___x_3348_, 2, v_inst_3332_);
lean_closure_set(v___x_3348_, 3, v_inst_3333_);
lean_closure_set(v___x_3348_, 4, v_inst_3334_);
lean_closure_set(v___x_3348_, 5, v_inst_3335_);
lean_closure_set(v___x_3348_, 6, v_inst_3336_);
lean_closure_set(v___x_3348_, 7, v_n_u2080_3337_);
lean_closure_set(v___x_3348_, 8, v_filter_3338_);
lean_closure_set(v___x_3348_, 9, v___x_3347_);
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3339_, v___x_3348_, v_aliases_3346_, v___x_3349_);
v___x_3351_ = lean_apply_4(v_toBind_3340_, lean_box(0), lean_box(0), v___x_3350_, v___f_3341_);
return v___x_3351_;
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
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_4018303539____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef);
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3876355841____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesExt);
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ResolveName_0__Lean_reservedNamePredsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ResolveName_0__Lean_reservedNamePredsExt);
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
