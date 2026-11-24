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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_revIter(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef;
static const lean_string_object l_Lean_registerReservedNamePredicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "failed to register reserved name suffix predicate, this operation can only be performed during initialization"};
static const lean_object* l_Lean_registerReservedNamePredicate___closed__0 = (const lean_object*)&l_Lean_registerReservedNamePredicate___closed__0_value;
static lean_once_cell_t l_Lean_registerReservedNamePredicate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerReservedNamePredicate___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ResolveName"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 177, 204, 170, 165, 172, 163, 11)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(196, 116, 196, 114, 71, 43, 230, 17)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__7_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 182, 208, 129, 167, 183, 199, 41)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "reservedNamePredsExt"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__10_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__8_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__9_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 95, 79, 214, 117, 203, 5, 233)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__10_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__10_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_reservedNamePredsExt;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedNameCandidate_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedNameCandidate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_isReservedNameCandidate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isReservedNameCandidate___closed__0;
LEAN_EXPORT uint8_t l_Lean_isReservedNameCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReservedNameCandidate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
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
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__6___boxed(lean_object**);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2_));
v___x_66_ = lean_st_mk_ref(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2_();
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
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object* v_isCandidate_73_, lean_object* v_isReserved_74_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_initializing();
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec_ref(v_isReserved_74_);
lean_dec_ref(v_isCandidate_73_);
v___x_77_ = lean_obj_once(&l_Lean_registerReservedNamePredicate___closed__1, &l_Lean_registerReservedNamePredicate___closed__1_once, _init_l_Lean_registerReservedNamePredicate___closed__1);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_79_ = l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef;
v___x_80_ = lean_st_ref_take(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v_isCandidate_73_);
lean_ctor_set(v___x_81_, 1, v_isReserved_74_);
v___x_82_ = lean_array_push(v___x_80_, v___x_81_);
v___x_83_ = lean_st_ref_put(v___x_79_, v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object* v_isCandidate_85_, lean_object* v_isReserved_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_registerReservedNamePredicate(v_isCandidate_85_, v_isReserved_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(lean_object* v___x_89_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_st_ref_get(v___x_89_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object* v___x_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(v___x_93_);
lean_dec(v___x_93_);
return v_res_95_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; 
v___x_96_ = l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef;
v___f_97_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; 
v___f_121_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_box(2);
v___x_124_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__10_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_));
v___x_125_ = 0;
v___x_126_ = 1;
v___x_127_ = l_Lean_registerEnvExtension___redArg(v___f_121_, v___x_122_, v___x_123_, v___x_124_, v___x_125_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2____boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1415357087____hygCtx___hyg_2_();
return v_res_129_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedNameCandidate_spec__0(lean_object* v_s_130_, lean_object* v_as_131_, size_t v_i_132_, size_t v_stop_133_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = lean_usize_dec_eq(v_i_132_, v_stop_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v_isCandidate_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_135_ = lean_array_uget_borrowed(v_as_131_, v_i_132_);
v_isCandidate_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_isCandidate_136_);
lean_inc_ref(v_s_130_);
v___x_137_ = lean_apply_1(v_isCandidate_136_, v_s_130_);
v___x_138_ = lean_unbox(v___x_137_);
if (v___x_138_ == 0)
{
size_t v___x_139_; size_t v___x_140_; 
v___x_139_ = ((size_t)1ULL);
v___x_140_ = lean_usize_add(v_i_132_, v___x_139_);
v_i_132_ = v___x_140_;
goto _start;
}
else
{
uint8_t v___x_142_; 
lean_dec_ref(v_s_130_);
v___x_142_ = lean_unbox(v___x_137_);
return v___x_142_;
}
}
else
{
uint8_t v___x_143_; 
lean_dec_ref(v_s_130_);
v___x_143_ = 0;
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedNameCandidate_spec__0___boxed(lean_object* v_s_144_, lean_object* v_as_145_, lean_object* v_i_146_, lean_object* v_stop_147_){
_start:
{
size_t v_i_boxed_148_; size_t v_stop_boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_i_boxed_148_ = lean_unbox_usize(v_i_146_);
lean_dec(v_i_146_);
v_stop_boxed_149_ = lean_unbox_usize(v_stop_147_);
lean_dec(v_stop_147_);
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedNameCandidate_spec__0(v_s_144_, v_as_145_, v_i_boxed_148_, v_stop_boxed_149_);
lean_dec_ref(v_as_145_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
static lean_object* _init_l_Lean_isReservedNameCandidate___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Array_instInhabited___redArg();
return v___x_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_isReservedNameCandidate(lean_object* v_env_153_, lean_object* v_s_154_){
_start:
{
lean_object* v___x_155_; lean_object* v_asyncMode_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_155_ = l___private_Lean_ResolveName_0__Lean_reservedNamePredsExt;
v_asyncMode_156_ = lean_ctor_get(v___x_155_, 2);
v___x_157_ = lean_obj_once(&l_Lean_isReservedNameCandidate___closed__0, &l_Lean_isReservedNameCandidate___closed__0_once, _init_l_Lean_isReservedNameCandidate___closed__0);
v___x_158_ = lean_box(0);
v___x_159_ = 0;
v___x_160_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_157_, v___x_155_, v_env_153_, v_asyncMode_156_, v___x_158_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v___x_160_);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v___x_160_);
lean_dec_ref(v_s_154_);
return v___x_163_;
}
else
{
if (v___x_163_ == 0)
{
lean_dec(v___x_160_);
lean_dec_ref(v_s_154_);
return v___x_163_;
}
else
{
size_t v___x_164_; size_t v___x_165_; uint8_t v___x_166_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_162_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedNameCandidate_spec__0(v_s_154_, v___x_160_, v___x_164_, v___x_165_);
lean_dec(v___x_160_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedNameCandidate___boxed(lean_object* v_env_167_, lean_object* v_s_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Lean_isReservedNameCandidate(v_env_167_, v_s_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_str_171_, lean_object* v_env_172_, lean_object* v_name_173_, lean_object* v_as_174_, size_t v_i_175_, size_t v_stop_176_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_eq(v_i_175_, v_stop_176_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v_isCandidate_183_; lean_object* v_isReserved_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_182_ = lean_array_uget_borrowed(v_as_174_, v_i_175_);
v_isCandidate_183_ = lean_ctor_get(v___x_182_, 0);
v_isReserved_184_ = lean_ctor_get(v___x_182_, 1);
lean_inc_ref(v_isCandidate_183_);
lean_inc_ref(v_str_171_);
v___x_185_ = lean_apply_1(v_isCandidate_183_, v_str_171_);
v___x_186_ = lean_unbox(v___x_185_);
if (v___x_186_ == 0)
{
goto v___jp_177_;
}
else
{
lean_object* v___x_187_; uint8_t v___x_188_; 
lean_inc_ref(v_isReserved_184_);
lean_inc(v_name_173_);
lean_inc_ref(v_env_172_);
v___x_187_ = lean_apply_2(v_isReserved_184_, v_env_172_, v_name_173_);
v___x_188_ = lean_unbox(v___x_187_);
if (v___x_188_ == 0)
{
goto v___jp_177_;
}
else
{
uint8_t v___x_189_; 
lean_dec(v_name_173_);
lean_dec_ref(v_env_172_);
lean_dec_ref(v_str_171_);
v___x_189_ = lean_unbox(v___x_187_);
return v___x_189_;
}
}
}
else
{
uint8_t v___x_190_; 
lean_dec(v_name_173_);
lean_dec_ref(v_env_172_);
lean_dec_ref(v_str_171_);
v___x_190_ = 0;
return v___x_190_;
}
v___jp_177_:
{
size_t v___x_178_; size_t v___x_179_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_175_, v___x_178_);
v_i_175_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_str_191_, lean_object* v_env_192_, lean_object* v_name_193_, lean_object* v_as_194_, lean_object* v_i_195_, lean_object* v_stop_196_){
_start:
{
size_t v_i_boxed_197_; size_t v_stop_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_i_boxed_197_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_stop_boxed_198_ = lean_unbox_usize(v_stop_196_);
lean_dec(v_stop_196_);
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_str_191_, v_env_192_, v_name_193_, v_as_194_, v_i_boxed_197_, v_stop_boxed_198_);
lean_dec_ref(v_as_194_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* v_env_201_, lean_object* v_name_202_){
_start:
{
if (lean_obj_tag(v_name_202_) == 1)
{
lean_object* v_str_203_; lean_object* v___x_204_; lean_object* v_asyncMode_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_str_203_ = lean_ctor_get(v_name_202_, 1);
lean_inc_ref(v_str_203_);
v___x_204_ = l___private_Lean_ResolveName_0__Lean_reservedNamePredsExt;
v_asyncMode_205_ = lean_ctor_get(v___x_204_, 2);
v___x_206_ = lean_obj_once(&l_Lean_isReservedNameCandidate___closed__0, &l_Lean_isReservedNameCandidate___closed__0_once, _init_l_Lean_isReservedNameCandidate___closed__0);
v___x_207_ = lean_box(0);
v___x_208_ = 0;
lean_inc_ref(v_env_201_);
v___x_209_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_206_, v___x_204_, v_env_201_, v_asyncMode_205_, v___x_207_, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_array_get_size(v___x_209_);
v___x_212_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec(v___x_209_);
lean_dec_ref_known(v_name_202_, 2);
lean_dec_ref(v_str_203_);
lean_dec_ref(v_env_201_);
return v___x_212_;
}
else
{
if (v___x_212_ == 0)
{
lean_dec(v___x_209_);
lean_dec_ref_known(v_name_202_, 2);
lean_dec_ref(v_str_203_);
lean_dec_ref(v_env_201_);
return v___x_212_;
}
else
{
size_t v___x_213_; size_t v___x_214_; uint8_t v___x_215_; 
v___x_213_ = ((size_t)0ULL);
v___x_214_ = lean_usize_of_nat(v___x_211_);
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_str_203_, v_env_201_, v_name_202_, v___x_209_, v___x_213_, v___x_214_);
lean_dec(v___x_209_);
return v___x_215_;
}
}
}
else
{
uint8_t v___x_216_; 
lean_dec(v_name_202_);
lean_dec_ref(v_env_201_);
v___x_216_ = 0;
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_217_, lean_object* v_name_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = lean_is_reserved_name(v_env_217_, v_name_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_ks_225_; lean_object* v_vs_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_250_; 
v_ks_225_ = lean_ctor_get(v_x_221_, 0);
v_vs_226_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_250_ == 0)
{
v___x_228_ = v_x_221_;
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_vs_226_);
lean_inc(v_ks_225_);
lean_dec(v_x_221_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_get_size(v_ks_225_);
v___x_231_ = lean_nat_dec_lt(v_x_222_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_x_222_);
v___x_232_ = lean_array_push(v_ks_225_, v_x_223_);
v___x_233_ = lean_array_push(v_vs_226_, v_x_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_233_);
lean_ctor_set(v___x_228_, 0, v___x_232_);
v___x_235_ = v___x_228_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
else
{
lean_object* v_k_x27_237_; uint8_t v___x_238_; 
v_k_x27_237_ = lean_array_fget_borrowed(v_ks_225_, v_x_222_);
v___x_238_ = lean_name_eq(v_x_223_, v_k_x27_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_240_; 
if (v_isShared_229_ == 0)
{
v___x_240_ = v___x_228_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_ks_225_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_vs_226_);
v___x_240_ = v_reuseFailAlloc_244_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_x_222_, v___x_241_);
lean_dec(v_x_222_);
v_x_221_ = v___x_240_;
v_x_222_ = v___x_242_;
goto _start;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_245_ = lean_array_fset(v_ks_225_, v_x_222_, v_x_223_);
v___x_246_ = lean_array_fset(v_vs_226_, v_x_222_, v_x_224_);
lean_dec(v_x_222_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_246_);
lean_ctor_set(v___x_228_, 0, v___x_245_);
v___x_248_ = v___x_228_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_251_, lean_object* v_k_252_, lean_object* v_v_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_251_, v___x_254_, v_k_252_, v_v_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_257_, size_t v_x_258_, size_t v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v_es_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v_j_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_es_262_ = lean_ctor_get(v_x_257_, 0);
v___x_263_ = ((size_t)31ULL);
v___x_264_ = lean_usize_land(v_x_258_, v___x_263_);
v_j_265_ = lean_usize_to_nat(v___x_264_);
v___x_266_ = lean_array_get_size(v_es_262_);
v___x_267_ = lean_nat_dec_lt(v_j_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_j_265_);
lean_dec(v_x_261_);
lean_dec(v_x_260_);
return v_x_257_;
}
else
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_306_; 
lean_inc_ref(v_es_262_);
v_isSharedCheck_306_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_x_257_, 0);
lean_dec(v_unused_307_);
v___x_269_ = v_x_257_;
v_isShared_270_ = v_isSharedCheck_306_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_x_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_306_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_v_271_; lean_object* v___x_272_; lean_object* v_xs_x27_273_; lean_object* v___y_275_; 
v_v_271_ = lean_array_fget(v_es_262_, v_j_265_);
v___x_272_ = lean_box(0);
v_xs_x27_273_ = lean_array_fset(v_es_262_, v_j_265_, v___x_272_);
switch(lean_obj_tag(v_v_271_))
{
case 0:
{
lean_object* v_key_280_; lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_291_; 
v_key_280_ = lean_ctor_get(v_v_271_, 0);
v_val_281_ = lean_ctor_get(v_v_271_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_v_271_);
if (v_isSharedCheck_291_ == 0)
{
v___x_283_ = v_v_271_;
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_inc(v_key_280_);
lean_dec(v_v_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
uint8_t v___x_285_; 
v___x_285_ = lean_name_eq(v_x_260_, v_key_280_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_del_object(v___x_283_);
v___x_286_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_280_, v_val_281_, v_x_260_, v_x_261_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___y_275_ = v___x_287_;
goto v___jp_274_;
}
else
{
lean_object* v___x_289_; 
lean_dec(v_val_281_);
lean_dec(v_key_280_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_x_261_);
lean_ctor_set(v___x_283_, 0, v_x_260_);
v___x_289_ = v___x_283_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_x_260_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_x_261_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
v___y_275_ = v___x_289_;
goto v___jp_274_;
}
}
}
}
case 1:
{
lean_object* v_node_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_304_; 
v_node_292_ = lean_ctor_get(v_v_271_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_v_271_);
if (v_isSharedCheck_304_ == 0)
{
v___x_294_ = v_v_271_;
v_isShared_295_ = v_isSharedCheck_304_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_node_292_);
lean_dec(v_v_271_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_304_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_usize_shift_right(v_x_258_, v___x_296_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_x_259_, v___x_298_);
v___x_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_292_, v___x_297_, v___x_299_, v_x_260_, v_x_261_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_300_);
v___x_302_ = v___x_294_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v___y_275_ = v___x_302_;
goto v___jp_274_;
}
}
}
default: 
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_x_260_);
lean_ctor_set(v___x_305_, 1, v_x_261_);
v___y_275_ = v___x_305_;
goto v___jp_274_;
}
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_array_fset(v_xs_x27_273_, v_j_265_, v___y_275_);
lean_dec(v_j_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_276_);
v___x_278_ = v___x_269_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
else
{
lean_object* v_ks_308_; lean_object* v_vs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_327_; 
v_ks_308_ = lean_ctor_get(v_x_257_, 0);
v_vs_309_ = lean_ctor_get(v_x_257_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_327_ == 0)
{
v___x_311_ = v_x_257_;
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_vs_309_);
lean_inc(v_ks_308_);
lean_dec(v_x_257_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_ks_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_vs_309_);
v___x_314_ = v_reuseFailAlloc_326_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v_newNode_315_; size_t v___x_316_; uint8_t v___x_317_; 
v_newNode_315_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_314_, v_x_260_, v_x_261_);
v___x_316_ = ((size_t)7ULL);
v___x_317_ = lean_usize_dec_le(v___x_316_, v_x_259_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_315_);
v___x_319_ = lean_unsigned_to_nat(4u);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
if (v___x_320_ == 0)
{
lean_object* v_ks_321_; lean_object* v_vs_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_ks_321_ = lean_ctor_get(v_newNode_315_, 0);
lean_inc_ref(v_ks_321_);
v_vs_322_ = lean_ctor_get(v_newNode_315_, 1);
lean_inc_ref(v_vs_322_);
lean_dec_ref(v_newNode_315_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_259_, v_ks_321_, v_vs_322_, v___x_323_, v___x_324_);
lean_dec_ref(v_vs_322_);
lean_dec_ref(v_ks_321_);
return v___x_325_;
}
else
{
return v_newNode_315_;
}
}
else
{
return v_newNode_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_328_, lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_i_331_, lean_object* v_entries_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_array_get_size(v_keys_329_);
v___x_334_ = lean_nat_dec_lt(v_i_331_, v___x_333_);
if (v___x_334_ == 0)
{
lean_dec(v_i_331_);
return v_entries_332_;
}
else
{
lean_object* v_k_335_; lean_object* v_v_336_; uint64_t v___y_338_; 
v_k_335_ = lean_array_fget_borrowed(v_keys_329_, v_i_331_);
v_v_336_ = lean_array_fget_borrowed(v_vals_330_, v_i_331_);
if (lean_obj_tag(v_k_335_) == 0)
{
uint64_t v___x_349_; 
v___x_349_ = 1723ULL;
v___y_338_ = v___x_349_;
goto v___jp_337_;
}
else
{
uint64_t v_hash_350_; 
v_hash_350_ = lean_ctor_get_uint64(v_k_335_, sizeof(void*)*2);
v___y_338_ = v_hash_350_;
goto v___jp_337_;
}
v___jp_337_:
{
size_t v_h_339_; size_t v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v_h_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_h_339_ = lean_uint64_to_usize(v___y_338_);
v___x_340_ = ((size_t)5ULL);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v_depth_328_, v___x_342_);
v___x_344_ = lean_usize_mul(v___x_340_, v___x_343_);
v_h_345_ = lean_usize_shift_right(v_h_339_, v___x_344_);
v___x_346_ = lean_nat_add(v_i_331_, v___x_341_);
lean_dec(v_i_331_);
lean_inc(v_v_336_);
lean_inc(v_k_335_);
v___x_347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_332_, v_h_345_, v_depth_328_, v_k_335_, v_v_336_);
v_i_331_ = v___x_346_;
v_entries_332_ = v___x_347_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_351_, lean_object* v_keys_352_, lean_object* v_vals_353_, lean_object* v_i_354_, lean_object* v_entries_355_){
_start:
{
size_t v_depth_boxed_356_; lean_object* v_res_357_; 
v_depth_boxed_356_ = lean_unbox_usize(v_depth_351_);
lean_dec(v_depth_351_);
v_res_357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_356_, v_keys_352_, v_vals_353_, v_i_354_, v_entries_355_);
lean_dec_ref(v_vals_353_);
lean_dec_ref(v_keys_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_1075__boxed_363_; size_t v_x_1076__boxed_364_; lean_object* v_res_365_; 
v_x_1075__boxed_363_ = lean_unbox_usize(v_x_359_);
lean_dec(v_x_359_);
v_x_1076__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_358_, v_x_1075__boxed_363_, v_x_1076__boxed_364_, v_x_361_, v_x_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
uint64_t v___y_370_; 
if (lean_obj_tag(v_x_367_) == 0)
{
uint64_t v___x_374_; 
v___x_374_ = 1723ULL;
v___y_370_ = v___x_374_;
goto v___jp_369_;
}
else
{
uint64_t v_hash_375_; 
v_hash_375_ = lean_ctor_get_uint64(v_x_367_, sizeof(void*)*2);
v___y_370_ = v_hash_375_;
goto v___jp_369_;
}
v___jp_369_:
{
size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_uint64_to_usize(v___y_370_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_366_, v___x_371_, v___x_372_, v_x_367_, v_x_368_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
return v_x_376_;
}
else
{
lean_object* v_key_378_; lean_object* v_value_379_; lean_object* v_tail_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_406_; 
v_key_378_ = lean_ctor_get(v_x_377_, 0);
v_value_379_ = lean_ctor_get(v_x_377_, 1);
v_tail_380_ = lean_ctor_get(v_x_377_, 2);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_406_ == 0)
{
v___x_382_ = v_x_377_;
v_isShared_383_ = v_isSharedCheck_406_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_tail_380_);
lean_inc(v_value_379_);
lean_inc(v_key_378_);
lean_dec(v_x_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_406_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; uint64_t v___y_386_; 
v___x_384_ = lean_array_get_size(v_x_376_);
if (lean_obj_tag(v_key_378_) == 0)
{
uint64_t v___x_404_; 
v___x_404_ = 1723ULL;
v___y_386_ = v___x_404_;
goto v___jp_385_;
}
else
{
uint64_t v_hash_405_; 
v_hash_405_ = lean_ctor_get_uint64(v_key_378_, sizeof(void*)*2);
v___y_386_ = v_hash_405_;
goto v___jp_385_;
}
v___jp_385_:
{
uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v_fold_389_; uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_387_ = 32ULL;
v___x_388_ = lean_uint64_shift_right(v___y_386_, v___x_387_);
v_fold_389_ = lean_uint64_xor(v___y_386_, v___x_388_);
v___x_390_ = 16ULL;
v___x_391_ = lean_uint64_shift_right(v_fold_389_, v___x_390_);
v___x_392_ = lean_uint64_xor(v_fold_389_, v___x_391_);
v___x_393_ = lean_uint64_to_usize(v___x_392_);
v___x_394_ = lean_usize_of_nat(v___x_384_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_sub(v___x_394_, v___x_395_);
v___x_397_ = lean_usize_land(v___x_393_, v___x_396_);
v___x_398_ = lean_array_uget_borrowed(v_x_376_, v___x_397_);
lean_inc(v___x_398_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 2, v___x_398_);
v___x_400_ = v___x_382_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_key_378_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_value_379_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v___x_398_);
v___x_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_array_uset(v_x_376_, v___x_397_, v___x_400_);
v_x_376_ = v___x_401_;
v_x_377_ = v_tail_380_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_407_, lean_object* v_source_408_, lean_object* v_target_409_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_source_408_);
v___x_411_ = lean_nat_dec_lt(v_i_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec_ref(v_source_408_);
lean_dec(v_i_407_);
return v_target_409_;
}
else
{
lean_object* v_es_412_; lean_object* v___x_413_; lean_object* v_source_414_; lean_object* v_target_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_es_412_ = lean_array_fget(v_source_408_, v_i_407_);
v___x_413_ = lean_box(0);
v_source_414_ = lean_array_fset(v_source_408_, v_i_407_, v___x_413_);
v_target_415_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_409_, v_es_412_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v_i_407_, v___x_416_);
lean_dec(v_i_407_);
v_i_407_ = v___x_417_;
v_source_408_ = v_source_414_;
v_target_409_ = v_target_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_nbuckets_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_420_ = lean_array_get_size(v_data_419_);
v___x_421_ = lean_unsigned_to_nat(2u);
v_nbuckets_422_ = lean_nat_mul(v___x_420_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_box(0);
v___x_425_ = lean_mk_array(v_nbuckets_422_, v___x_424_);
v___x_426_ = lean_array_propagate_mark(v_data_419_, v___x_425_);
v___x_427_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_423_, v_data_419_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_tail_432_; uint8_t v___x_433_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
v___x_433_ = lean_name_eq(v_key_431_, v_a_428_);
if (v___x_433_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_439_, lean_object* v_b_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_dec(v_b_440_);
lean_dec(v_a_439_);
return v_x_441_;
}
else
{
lean_object* v_key_442_; lean_object* v_value_443_; lean_object* v_tail_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_456_; 
v_key_442_ = lean_ctor_get(v_x_441_, 0);
v_value_443_ = lean_ctor_get(v_x_441_, 1);
v_tail_444_ = lean_ctor_get(v_x_441_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_456_ == 0)
{
v___x_446_ = v_x_441_;
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_tail_444_);
lean_inc(v_value_443_);
lean_inc(v_key_442_);
lean_dec(v_x_441_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; 
v___x_448_ = lean_name_eq(v_key_442_, v_a_439_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_439_, v_b_440_, v_tail_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 2, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_key_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_value_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v_value_443_);
lean_dec(v_key_442_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_b_440_);
lean_ctor_set(v___x_446_, 0, v_a_439_);
v___x_454_ = v___x_446_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_b_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_tail_444_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_457_, lean_object* v_a_458_, lean_object* v_b_459_){
_start:
{
lean_object* v_size_460_; lean_object* v_buckets_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_507_; 
v_size_460_ = lean_ctor_get(v_m_457_, 0);
v_buckets_461_ = lean_ctor_get(v_m_457_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_m_457_);
if (v_isSharedCheck_507_ == 0)
{
v___x_463_ = v_m_457_;
v_isShared_464_ = v_isSharedCheck_507_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_buckets_461_);
lean_inc(v_size_460_);
lean_dec(v_m_457_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_507_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; uint64_t v___y_467_; 
v___x_465_ = lean_array_get_size(v_buckets_461_);
if (lean_obj_tag(v_a_458_) == 0)
{
uint64_t v___x_505_; 
v___x_505_ = 1723ULL;
v___y_467_ = v___x_505_;
goto v___jp_466_;
}
else
{
uint64_t v_hash_506_; 
v_hash_506_ = lean_ctor_get_uint64(v_a_458_, sizeof(void*)*2);
v___y_467_ = v_hash_506_;
goto v___jp_466_;
}
v___jp_466_:
{
uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v_fold_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; lean_object* v_bkt_479_; uint8_t v___x_480_; 
v___x_468_ = 32ULL;
v___x_469_ = lean_uint64_shift_right(v___y_467_, v___x_468_);
v_fold_470_ = lean_uint64_xor(v___y_467_, v___x_469_);
v___x_471_ = 16ULL;
v___x_472_ = lean_uint64_shift_right(v_fold_470_, v___x_471_);
v___x_473_ = lean_uint64_xor(v_fold_470_, v___x_472_);
v___x_474_ = lean_uint64_to_usize(v___x_473_);
v___x_475_ = lean_usize_of_nat(v___x_465_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_sub(v___x_475_, v___x_476_);
v___x_478_ = lean_usize_land(v___x_474_, v___x_477_);
v_bkt_479_ = lean_array_uget_borrowed(v_buckets_461_, v___x_478_);
v___x_480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_458_, v_bkt_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v_size_x27_482_; lean_object* v___x_483_; lean_object* v_buckets_x27_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v_size_x27_482_ = lean_nat_add(v_size_460_, v___x_481_);
lean_dec(v_size_460_);
lean_inc(v_bkt_479_);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v_a_458_);
lean_ctor_set(v___x_483_, 1, v_b_459_);
lean_ctor_set(v___x_483_, 2, v_bkt_479_);
v_buckets_x27_484_ = lean_array_uset(v_buckets_461_, v___x_478_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(4u);
v___x_486_ = lean_nat_mul(v_size_x27_482_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_nat_div(v___x_486_, v___x_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_array_get_size(v_buckets_x27_484_);
v___x_490_ = lean_nat_dec_le(v___x_488_, v___x_489_);
lean_dec(v___x_488_);
if (v___x_490_ == 0)
{
lean_object* v_val_491_; lean_object* v___x_493_; 
v_val_491_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_484_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_val_491_);
lean_ctor_set(v___x_463_, 0, v_size_x27_482_);
v___x_493_ = v___x_463_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_x27_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_val_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_496_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_buckets_x27_484_);
lean_ctor_set(v___x_463_, 0, v_size_x27_482_);
v___x_496_ = v___x_463_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_size_x27_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_buckets_x27_484_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v___x_498_; lean_object* v_buckets_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_inc(v_bkt_479_);
v___x_498_ = lean_box(0);
v_buckets_x27_499_ = lean_array_uset(v_buckets_461_, v___x_478_, v___x_498_);
v___x_500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_458_, v_b_459_, v_bkt_479_);
v___x_501_ = lean_array_uset(v_buckets_x27_499_, v___x_478_, v___x_500_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_501_);
v___x_503_ = v___x_463_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_size_460_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_stage_u2081_511_; 
v_stage_u2081_511_ = lean_ctor_get_uint8(v_x_508_, sizeof(void*)*2);
if (v_stage_u2081_511_ == 0)
{
lean_object* v_map_u2081_512_; lean_object* v_map_u2082_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_map_u2081_512_ = lean_ctor_get(v_x_508_, 0);
v_map_u2082_513_ = lean_ctor_get(v_x_508_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v_x_508_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_map_u2082_513_);
lean_inc(v_map_u2081_512_);
lean_dec(v_x_508_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_513_, v_x_509_, v_x_510_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_map_u2081_512_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_520_, sizeof(void*)*2, v_stage_u2081_511_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_map_u2081_522_; lean_object* v_map_u2082_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_map_u2081_522_ = lean_ctor_get(v_x_508_, 0);
v_map_u2082_523_ = lean_ctor_get(v_x_508_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_531_ == 0)
{
v___x_525_ = v_x_508_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_map_u2082_523_);
lean_inc(v_map_u2081_522_);
lean_dec(v_x_508_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_522_, v_x_509_, v_x_510_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_map_u2082_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*2, v_stage_u2081_511_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v___x_534_; 
v___x_534_ = lean_box(0);
return v___x_534_;
}
else
{
lean_object* v_key_535_; lean_object* v_value_536_; lean_object* v_tail_537_; uint8_t v___x_538_; 
v_key_535_ = lean_ctor_get(v_x_533_, 0);
v_value_536_ = lean_ctor_get(v_x_533_, 1);
v_tail_537_ = lean_ctor_get(v_x_533_, 2);
v___x_538_ = lean_name_eq(v_key_535_, v_a_532_);
if (v___x_538_ == 0)
{
v_x_533_ = v_tail_537_;
goto _start;
}
else
{
lean_object* v___x_540_; 
lean_inc(v_value_536_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_value_536_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_541_, v_x_542_);
lean_dec(v_x_542_);
lean_dec(v_a_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_buckets_546_; lean_object* v___x_547_; uint64_t v___y_549_; 
v_buckets_546_ = lean_ctor_get(v_m_544_, 1);
v___x_547_ = lean_array_get_size(v_buckets_546_);
if (lean_obj_tag(v_a_545_) == 0)
{
uint64_t v___x_563_; 
v___x_563_ = 1723ULL;
v___y_549_ = v___x_563_;
goto v___jp_548_;
}
else
{
uint64_t v_hash_564_; 
v_hash_564_ = lean_ctor_get_uint64(v_a_545_, sizeof(void*)*2);
v___y_549_ = v_hash_564_;
goto v___jp_548_;
}
v___jp_548_:
{
uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v_fold_552_; uint64_t v___x_553_; uint64_t v___x_554_; uint64_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_550_ = 32ULL;
v___x_551_ = lean_uint64_shift_right(v___y_549_, v___x_550_);
v_fold_552_ = lean_uint64_xor(v___y_549_, v___x_551_);
v___x_553_ = 16ULL;
v___x_554_ = lean_uint64_shift_right(v_fold_552_, v___x_553_);
v___x_555_ = lean_uint64_xor(v_fold_552_, v___x_554_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
v___x_557_ = lean_usize_of_nat(v___x_547_);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_sub(v___x_557_, v___x_558_);
v___x_560_ = lean_usize_land(v___x_556_, v___x_559_);
v___x_561_ = lean_array_uget_borrowed(v_buckets_546_, v___x_560_);
v___x_562_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_545_, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_m_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_568_, lean_object* v_vals_569_, lean_object* v_i_570_, lean_object* v_k_571_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_get_size(v_keys_568_);
v___x_573_ = lean_nat_dec_lt(v_i_570_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v_i_570_);
v___x_574_ = lean_box(0);
return v___x_574_;
}
else
{
lean_object* v_k_x27_575_; uint8_t v___x_576_; 
v_k_x27_575_ = lean_array_fget_borrowed(v_keys_568_, v_i_570_);
v___x_576_ = lean_name_eq(v_k_571_, v_k_x27_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_i_570_, v___x_577_);
lean_dec(v_i_570_);
v_i_570_ = v___x_578_;
goto _start;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_array_fget_borrowed(v_vals_569_, v_i_570_);
lean_dec(v_i_570_);
lean_inc(v___x_580_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_i_584_, lean_object* v_k_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_582_, v_vals_583_, v_i_584_, v_k_585_);
lean_dec(v_k_585_);
lean_dec_ref(v_vals_583_);
lean_dec_ref(v_keys_582_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_587_, size_t v_x_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v_es_590_; lean_object* v___x_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v_j_594_; lean_object* v___x_595_; 
v_es_590_ = lean_ctor_get(v_x_587_, 0);
v___x_591_ = lean_box(2);
v___x_592_ = ((size_t)31ULL);
v___x_593_ = lean_usize_land(v_x_588_, v___x_592_);
v_j_594_ = lean_usize_to_nat(v___x_593_);
v___x_595_ = lean_array_get_borrowed(v___x_591_, v_es_590_, v_j_594_);
lean_dec(v_j_594_);
switch(lean_obj_tag(v___x_595_))
{
case 0:
{
lean_object* v_key_596_; lean_object* v_val_597_; uint8_t v___x_598_; 
v_key_596_ = lean_ctor_get(v___x_595_, 0);
v_val_597_ = lean_ctor_get(v___x_595_, 1);
v___x_598_ = lean_name_eq(v_x_589_, v_key_596_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
lean_object* v___x_600_; 
lean_inc(v_val_597_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_val_597_);
return v___x_600_;
}
}
case 1:
{
lean_object* v_node_601_; size_t v___x_602_; size_t v___x_603_; 
v_node_601_ = lean_ctor_get(v___x_595_, 0);
v___x_602_ = ((size_t)5ULL);
v___x_603_ = lean_usize_shift_right(v_x_588_, v___x_602_);
v_x_587_ = v_node_601_;
v_x_588_ = v___x_603_;
goto _start;
}
default: 
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(0);
return v___x_605_;
}
}
}
else
{
lean_object* v_ks_606_; lean_object* v_vs_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_ks_606_ = lean_ctor_get(v_x_587_, 0);
v_vs_607_ = lean_ctor_get(v_x_587_, 1);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_606_, v_vs_607_, v___x_608_, v_x_589_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_1579__boxed_613_; lean_object* v_res_614_; 
v_x_1579__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_614_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_610_, v_x_1579__boxed_613_, v_x_612_);
lean_dec(v_x_612_);
lean_dec_ref(v_x_610_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
uint64_t v___y_618_; 
if (lean_obj_tag(v_x_616_) == 0)
{
uint64_t v___x_621_; 
v___x_621_ = 1723ULL;
v___y_618_ = v___x_621_;
goto v___jp_617_;
}
else
{
uint64_t v_hash_622_; 
v_hash_622_ = lean_ctor_get_uint64(v_x_616_, sizeof(void*)*2);
v___y_618_ = v_hash_622_;
goto v___jp_617_;
}
v___jp_617_:
{
size_t v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_uint64_to_usize(v___y_618_);
v___x_620_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_615_, v___x_619_, v_x_616_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_623_, v_x_624_);
lean_dec(v_x_624_);
lean_dec_ref(v_x_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
uint8_t v_stage_u2081_628_; 
v_stage_u2081_628_ = lean_ctor_get_uint8(v_x_626_, sizeof(void*)*2);
if (v_stage_u2081_628_ == 0)
{
lean_object* v_map_u2081_629_; lean_object* v_map_u2082_630_; lean_object* v___x_631_; 
v_map_u2081_629_ = lean_ctor_get(v_x_626_, 0);
v_map_u2082_630_ = lean_ctor_get(v_x_626_, 1);
v___x_631_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_630_, v_x_627_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_629_, v_x_627_);
return v___x_632_;
}
else
{
return v___x_631_;
}
}
else
{
lean_object* v_map_u2081_633_; lean_object* v___x_634_; 
v_map_u2081_633_ = lean_ctor_get(v_x_626_, 0);
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_633_, v_x_627_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_635_, v_x_636_);
lean_dec(v_x_636_);
lean_dec_ref(v_x_635_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
uint8_t v___x_640_; 
v___x_640_ = 0;
return v___x_640_;
}
else
{
lean_object* v_head_641_; lean_object* v_tail_642_; uint8_t v___x_643_; 
v_head_641_ = lean_ctor_get(v_x_639_, 0);
v_tail_642_ = lean_ctor_get(v_x_639_, 1);
v___x_643_ = lean_name_eq(v_a_638_, v_head_641_);
if (v___x_643_ == 0)
{
v_x_639_ = v_tail_642_;
goto _start;
}
else
{
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_645_, lean_object* v_x_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_645_, v_x_646_);
lean_dec(v_x_646_);
lean_dec(v_a_645_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_649_, lean_object* v_e_650_){
_start:
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_668_; 
v_fst_651_ = lean_ctor_get(v_e_650_, 0);
v_snd_652_ = lean_ctor_get(v_e_650_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_e_650_);
if (v_isSharedCheck_668_ == 0)
{
v___x_654_ = v_e_650_;
v_isShared_655_ = v_isSharedCheck_668_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
lean_dec(v_e_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_668_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_649_, v_fst_651_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 1, v___x_657_);
lean_ctor_set(v___x_654_, 0, v_snd_652_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_snd_652_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_661_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_649_, v_fst_651_, v___x_659_);
return v___x_660_;
}
}
else
{
lean_object* v_val_662_; uint8_t v___x_663_; 
v_val_662_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v___x_656_, 1);
v___x_663_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_652_, v_val_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_665_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 1, v_val_662_);
lean_ctor_set(v___x_654_, 0, v_snd_652_);
v___x_665_ = v___x_654_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_snd_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_val_662_);
v___x_665_ = v_reuseFailAlloc_667_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_649_, v_fst_651_, v___x_665_);
return v___x_666_;
}
}
else
{
lean_dec(v_val_662_);
lean_del_object(v___x_654_);
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
return v_s_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_673_, v_x_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_x_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_678_, v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_686_, v_x_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec_ref(v_x_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_690_, lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_691_, v_a_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_694_, lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_694_, v_m_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_m_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_699_, v_x_700_, v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_703_, lean_object* v_m_704_, lean_object* v_a_705_, lean_object* v_b_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_704_, v_a_705_, v_b_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, size_t v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_709_, v_x_710_, v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
size_t v_x_1744__boxed_717_; lean_object* v_res_718_; 
v_x_1744__boxed_717_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_res_718_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_713_, v_x_714_, v_x_1744__boxed_717_, v_x_716_);
lean_dec(v_x_716_);
lean_dec_ref(v_x_714_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_719_, lean_object* v_a_720_, lean_object* v_x_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_720_, v_x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_723_, lean_object* v_a_724_, lean_object* v_x_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_723_, v_a_724_, v_x_725_);
lean_dec(v_x_725_);
lean_dec(v_a_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, size_t v_x_729_, size_t v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_728_, v_x_729_, v_x_730_, v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
size_t v_x_1760__boxed_740_; size_t v_x_1761__boxed_741_; lean_object* v_res_742_; 
v_x_1760__boxed_740_ = lean_unbox_usize(v_x_736_);
lean_dec(v_x_736_);
v_x_1761__boxed_741_ = lean_unbox_usize(v_x_737_);
lean_dec(v_x_737_);
v_res_742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_734_, v_x_735_, v_x_1760__boxed_740_, v_x_1761__boxed_741_, v_x_738_, v_x_739_);
return v_res_742_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_743_, lean_object* v_a_744_, lean_object* v_x_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_744_, v_x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_747_, lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_747_, v_a_748_, v_x_749_);
lean_dec(v_x_749_);
lean_dec(v_a_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_752_, lean_object* v_data_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_755_, lean_object* v_a_756_, lean_object* v_b_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_756_, v_b_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_760_, lean_object* v_keys_761_, lean_object* v_vals_762_, lean_object* v_heq_763_, lean_object* v_i_764_, lean_object* v_k_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_761_, v_vals_762_, v_i_764_, v_k_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_767_, lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_heq_770_, lean_object* v_i_771_, lean_object* v_k_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_767_, v_keys_768_, v_vals_769_, v_heq_770_, v_i_771_, v_k_772_);
lean_dec(v_k_772_);
lean_dec_ref(v_vals_769_);
lean_dec_ref(v_keys_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_774_, lean_object* v_n_775_, lean_object* v_k_776_, lean_object* v_v_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_775_, v_k_776_, v_v_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_779_, size_t v_depth_780_, lean_object* v_keys_781_, lean_object* v_vals_782_, lean_object* v_heq_783_, lean_object* v_i_784_, lean_object* v_entries_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_780_, v_keys_781_, v_vals_782_, v_i_784_, v_entries_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_787_, lean_object* v_depth_788_, lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_heq_791_, lean_object* v_i_792_, lean_object* v_entries_793_){
_start:
{
size_t v_depth_boxed_794_; lean_object* v_res_795_; 
v_depth_boxed_794_ = lean_unbox_usize(v_depth_788_);
lean_dec(v_depth_788_);
v_res_795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_787_, v_depth_boxed_794_, v_keys_789_, v_vals_790_, v_heq_791_, v_i_792_, v_entries_793_);
lean_dec_ref(v_vals_790_);
lean_dec_ref(v_keys_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_796_, lean_object* v_i_797_, lean_object* v_source_798_, lean_object* v_target_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_797_, v_source_798_, v_target_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_802_, v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_811_){
_start:
{
uint8_t v_stage_u2081_812_; 
v_stage_u2081_812_ = lean_ctor_get_uint8(v_m_811_, sizeof(void*)*2);
if (v_stage_u2081_812_ == 0)
{
return v_m_811_;
}
else
{
lean_object* v_map_u2081_813_; lean_object* v_map_u2082_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
v_map_u2081_813_ = lean_ctor_get(v_m_811_, 0);
v_map_u2082_814_ = lean_ctor_get(v_m_811_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_m_811_);
if (v_isSharedCheck_822_ == 0)
{
v___x_816_ = v_m_811_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_map_u2082_814_);
lean_inc(v_map_u2081_813_);
lean_dec(v_m_811_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v___x_818_; lean_object* v___x_820_; 
v___x_818_ = 0;
if (v_isShared_817_ == 0)
{
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_map_u2081_813_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_map_u2082_814_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*2, v___x_818_);
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_823_, lean_object* v_m_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_array_mk(v_es_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_828_, size_t v_i_829_, size_t v_stop_830_, lean_object* v_b_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_eq(v_i_829_, v_stop_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; size_t v___x_835_; size_t v___x_836_; 
v___x_833_ = lean_array_uget_borrowed(v_as_828_, v_i_829_);
lean_inc(v___x_833_);
v___x_834_ = l_Lean_addAliasEntry(v_b_831_, v___x_833_);
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_829_, v___x_835_);
v_i_829_ = v___x_836_;
v_b_831_ = v___x_834_;
goto _start;
}
else
{
return v_b_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_838_, lean_object* v_i_839_, lean_object* v_stop_840_, lean_object* v_b_841_){
_start:
{
size_t v_i_boxed_842_; size_t v_stop_boxed_843_; lean_object* v_res_844_; 
v_i_boxed_842_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_stop_boxed_843_ = lean_unbox_usize(v_stop_840_);
lean_dec(v_stop_840_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_838_, v_i_boxed_842_, v_stop_boxed_843_, v_b_841_);
lean_dec_ref(v_as_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_845_, size_t v_i_846_, size_t v_stop_847_, lean_object* v_b_848_){
_start:
{
lean_object* v___y_850_; uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_eq(v_i_846_, v_stop_847_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_855_ = lean_array_uget_borrowed(v_as_845_, v_i_846_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v___x_855_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_850_ = v_b_848_;
goto v___jp_849_;
}
else
{
size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = ((size_t)0ULL);
v___x_860_ = lean_usize_of_nat(v___x_857_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_855_, v___x_859_, v___x_860_, v_b_848_);
v___y_850_ = v___x_861_;
goto v___jp_849_;
}
}
else
{
return v_b_848_;
}
v___jp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_846_, v___x_851_);
v_i_846_ = v___x_852_;
v_b_848_ = v___y_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_862_, lean_object* v_i_863_, lean_object* v_stop_864_, lean_object* v_b_865_){
_start:
{
size_t v_i_boxed_866_; size_t v_stop_boxed_867_; lean_object* v_res_868_; 
v_i_boxed_866_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_stop_boxed_867_ = lean_unbox_usize(v_stop_864_);
lean_dec(v_stop_864_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_862_, v_i_boxed_866_, v_stop_boxed_867_, v_b_865_);
lean_dec_ref(v_as_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_869_, lean_object* v_as_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_size(v_as_870_);
v___x_873_ = lean_nat_dec_lt(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
return v_initState_869_;
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_872_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_870_, v___x_874_, v___x_875_, v_initState_869_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_877_, lean_object* v_as_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_877_, v_as_878_);
lean_dec_ref(v_as_878_);
return v_res_879_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_box(0);
v___x_881_ = lean_unsigned_to_nat(16u);
v___x_882_ = lean_mk_array(v___x_881_, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; 
v___x_889_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_890_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_891_ = 1;
v___x_892_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_889_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_893_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_895_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_894_, v_es_893_);
v___x_896_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_897_);
lean_dec_ref(v_es_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_916_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias___lam__0(lean_object* v_addEntryFn_919_, lean_object* v___x_920_, lean_object* v_s_921_){
_start:
{
lean_object* v_importedEntries_922_; lean_object* v_state_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_931_; 
v_importedEntries_922_ = lean_ctor_get(v_s_921_, 0);
v_state_923_ = lean_ctor_get(v_s_921_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_s_921_);
if (v_isSharedCheck_931_ == 0)
{
v___x_925_ = v_s_921_;
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_state_923_);
lean_inc(v_importedEntries_922_);
lean_dec(v_s_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_state_927_; lean_object* v___x_929_; 
v_state_927_ = lean_apply_2(v_addEntryFn_919_, v_state_923_, v___x_920_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v_state_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_importedEntries_922_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_state_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_932_, lean_object* v_a_933_, lean_object* v_e_934_){
_start:
{
lean_object* v___x_935_; lean_object* v_toEnvExtension_936_; lean_object* v_addEntryFn_937_; lean_object* v_asyncMode_938_; uint8_t v_logWrites_939_; lean_object* v___x_940_; lean_object* v___f_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_935_ = l_Lean_aliasExtension;
v_toEnvExtension_936_ = lean_ctor_get(v___x_935_, 0);
v_addEntryFn_937_ = lean_ctor_get(v___x_935_, 3);
v_asyncMode_938_ = lean_ctor_get(v_toEnvExtension_936_, 2);
v_logWrites_939_ = lean_ctor_get_uint8(v_toEnvExtension_936_, sizeof(void*)*6);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_a_933_);
lean_ctor_set(v___x_940_, 1, v_e_934_);
lean_inc(v_addEntryFn_937_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_addAlias___lam__0), 3, 2);
lean_closure_set(v___f_941_, 0, v_addEntryFn_937_);
lean_closure_set(v___f_941_, 1, v___x_940_);
v___x_942_ = lean_box(0);
v___x_943_ = 1;
if (v_logWrites_939_ == 0)
{
lean_object* v___x_944_; 
lean_inc_ref(v_toEnvExtension_936_);
v___x_944_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_936_, v_env_932_, v___f_941_, v_asyncMode_938_, v___x_942_, v___x_943_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_inc_ref_n(v_toEnvExtension_936_, 2);
v___x_945_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_936_, v_env_932_);
lean_dec_ref(v_env_932_);
v___x_946_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_936_, v___x_945_, v___f_941_, v_asyncMode_938_, v___x_942_, v___x_943_);
return v___x_946_;
}
}
}
static lean_object* _init_l_Lean_getAliasState___closed__0(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_SMap_instInhabited___redArg();
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_948_){
_start:
{
lean_object* v___x_949_; lean_object* v_toEnvExtension_950_; lean_object* v_asyncMode_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = l_Lean_aliasExtension;
v_toEnvExtension_950_ = lean_ctor_get(v___x_949_, 0);
v_asyncMode_951_ = lean_ctor_get(v_toEnvExtension_950_, 2);
v___x_952_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_952_, v___x_949_, v_env_948_, v_asyncMode_951_, v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_955_, uint8_t v_skipProtected_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
if (lean_obj_tag(v_a_957_) == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_env_955_);
v___x_959_ = l_List_reverse___redArg(v_a_958_);
return v___x_959_;
}
else
{
lean_object* v_head_960_; lean_object* v_tail_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_972_; 
v_head_960_ = lean_ctor_get(v_a_957_, 0);
v_tail_961_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_972_ == 0)
{
v___x_963_ = v_a_957_;
v_isShared_964_ = v_isSharedCheck_972_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_tail_961_);
lean_inc(v_head_960_);
lean_dec(v_a_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_972_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
lean_inc(v_head_960_);
lean_inc_ref(v_env_955_);
v___x_965_ = l_Lean_isProtected(v_env_955_, v_head_960_);
if (v___x_965_ == 0)
{
if (v_skipProtected_956_ == 0)
{
lean_del_object(v___x_963_);
lean_dec(v_head_960_);
v_a_957_ = v_tail_961_;
goto _start;
}
else
{
lean_object* v___x_968_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_a_958_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_head_960_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_a_958_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v_a_957_ = v_tail_961_;
v_a_958_ = v___x_968_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_963_);
lean_dec(v_head_960_);
v_a_957_ = v_tail_961_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_973_, lean_object* v_skipProtected_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
uint8_t v_skipProtected_boxed_977_; lean_object* v_res_978_; 
v_skipProtected_boxed_977_ = lean_unbox(v_skipProtected_974_);
v_res_978_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_973_, v_skipProtected_boxed_977_, v_a_975_, v_a_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_979_, lean_object* v_a_980_, uint8_t v_skipProtected_981_){
_start:
{
lean_object* v___x_982_; lean_object* v_toEnvExtension_983_; lean_object* v_asyncMode_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_982_ = l_Lean_aliasExtension;
v_toEnvExtension_983_ = lean_ctor_get(v___x_982_, 0);
v_asyncMode_984_ = lean_ctor_get(v_toEnvExtension_983_, 2);
v___x_985_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_986_ = lean_box(0);
lean_inc_ref(v_env_979_);
v___x_987_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_985_, v___x_982_, v_env_979_, v_asyncMode_984_, v___x_986_);
v___x_988_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_987_, v_a_980_);
lean_dec(v___x_987_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v_env_979_);
v___x_989_ = lean_box(0);
return v___x_989_;
}
else
{
if (v_skipProtected_981_ == 0)
{
lean_object* v_val_990_; 
lean_dec_ref(v_env_979_);
v_val_990_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v___x_988_, 1);
return v_val_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_val_991_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_988_, 1);
v___x_992_ = lean_box(0);
v___x_993_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_979_, v_skipProtected_981_, v_val_991_, v___x_992_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_994_, lean_object* v_a_995_, lean_object* v_skipProtected_996_){
_start:
{
uint8_t v_skipProtected_boxed_997_; lean_object* v_res_998_; 
v_skipProtected_boxed_997_ = lean_unbox(v_skipProtected_996_);
v_res_998_ = l_Lean_getAliases(v_env_994_, v_a_995_, v_skipProtected_boxed_997_);
lean_dec(v_a_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_999_, lean_object* v_as_1000_, lean_object* v_a_1001_, lean_object* v_es_1002_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_999_, v_es_1002_);
if (v___x_1003_ == 0)
{
lean_dec(v_a_1001_);
return v_as_1000_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_a_1001_);
lean_ctor_set(v___x_1004_, 1, v_as_1000_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_1005_, lean_object* v_as_1006_, lean_object* v_a_1007_, lean_object* v_es_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_getRevAliases___lam__0(v_e_1005_, v_as_1006_, v_a_1007_, v_es_1008_);
lean_dec(v_es_1008_);
lean_dec(v_e_1005_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_1010_, lean_object* v_keys_1011_, lean_object* v_vals_1012_, lean_object* v_i_1013_, lean_object* v_acc_1014_){
_start:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_array_get_size(v_keys_1011_);
v___x_1016_ = lean_nat_dec_lt(v_i_1013_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec(v_i_1013_);
lean_dec(v_f_1010_);
return v_acc_1014_;
}
else
{
lean_object* v_k_1017_; lean_object* v_v_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_k_1017_ = lean_array_fget_borrowed(v_keys_1011_, v_i_1013_);
v_v_1018_ = lean_array_fget_borrowed(v_vals_1012_, v_i_1013_);
lean_inc(v_f_1010_);
lean_inc(v_v_1018_);
lean_inc(v_k_1017_);
v___x_1019_ = lean_apply_3(v_f_1010_, v_acc_1014_, v_k_1017_, v_v_1018_);
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1013_, v___x_1020_);
lean_dec(v_i_1013_);
v_i_1013_ = v___x_1021_;
v_acc_1014_ = v___x_1019_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_1023_, lean_object* v_keys_1024_, lean_object* v_vals_1025_, lean_object* v_i_1026_, lean_object* v_acc_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1023_, v_keys_1024_, v_vals_1025_, v_i_1026_, v_acc_1027_);
lean_dec_ref(v_vals_1025_);
lean_dec_ref(v_keys_1024_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1029_, lean_object* v_as_1030_, size_t v_i_1031_, size_t v_stop_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v___y_1035_; uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1031_, v_stop_1032_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1030_, v_i_1031_);
switch(lean_obj_tag(v___x_1040_))
{
case 0:
{
lean_object* v_key_1041_; lean_object* v_val_1042_; lean_object* v___x_1043_; 
v_key_1041_ = lean_ctor_get(v___x_1040_, 0);
v_val_1042_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_f_1029_);
lean_inc(v_val_1042_);
lean_inc(v_key_1041_);
v___x_1043_ = lean_apply_3(v_f_1029_, v_b_1033_, v_key_1041_, v_val_1042_);
v___y_1035_ = v___x_1043_;
goto v___jp_1034_;
}
case 1:
{
lean_object* v_node_1044_; lean_object* v___x_1045_; 
v_node_1044_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_f_1029_);
v___x_1045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1029_, v_node_1044_, v_b_1033_);
v___y_1035_ = v___x_1045_;
goto v___jp_1034_;
}
default: 
{
v___y_1035_ = v_b_1033_;
goto v___jp_1034_;
}
}
}
else
{
lean_dec(v_f_1029_);
return v_b_1033_;
}
v___jp_1034_:
{
size_t v___x_1036_; size_t v___x_1037_; 
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1031_, v___x_1036_);
v_i_1031_ = v___x_1037_;
v_b_1033_ = v___y_1035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v_es_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_es_1049_ = lean_ctor_get(v_x_1047_, 0);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_array_get_size(v_es_1049_);
v___x_1052_ = lean_nat_dec_lt(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_dec(v_f_1046_);
return v_x_1048_;
}
else
{
size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = lean_usize_of_nat(v___x_1051_);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1046_, v_es_1049_, v___x_1053_, v___x_1054_, v_x_1048_);
return v___x_1055_;
}
}
else
{
lean_object* v_ks_1056_; lean_object* v_vs_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_ks_1056_ = lean_ctor_get(v_x_1047_, 0);
v_vs_1057_ = lean_ctor_get(v_x_1047_, 1);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1046_, v_ks_1056_, v_vs_1057_, v___x_1058_, v_x_1048_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1060_, v_x_1061_, v_x_1062_);
lean_dec_ref(v_x_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_1064_, lean_object* v_as_1065_, lean_object* v_i_1066_, lean_object* v_stop_1067_, lean_object* v_b_1068_){
_start:
{
size_t v_i_boxed_1069_; size_t v_stop_boxed_1070_; lean_object* v_res_1071_; 
v_i_boxed_1069_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_stop_boxed_1070_ = lean_unbox_usize(v_stop_1067_);
lean_dec(v_stop_1067_);
v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1064_, v_as_1065_, v_i_boxed_1069_, v_stop_boxed_1070_, v_b_1068_);
lean_dec_ref(v_as_1065_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1072_, lean_object* v_x1_1073_, lean_object* v_x2_1074_, lean_object* v_x3_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_apply_3(v_f_1072_, v_x1_1073_, v_x2_1074_, v_x3_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1077_, lean_object* v_f_1078_, lean_object* v_init_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1080_, 0, v_f_1078_);
v___x_1081_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1080_, v_map_1077_, v_init_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1082_, lean_object* v_f_1083_, lean_object* v_init_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1082_, v_f_1083_, v_init_1084_);
lean_dec_ref(v_map_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_dec(v_f_1086_);
return v_x_1087_;
}
else
{
lean_object* v_key_1089_; lean_object* v_value_1090_; lean_object* v_tail_1091_; lean_object* v___x_1092_; 
v_key_1089_ = lean_ctor_get(v_x_1088_, 0);
lean_inc(v_key_1089_);
v_value_1090_ = lean_ctor_get(v_x_1088_, 1);
lean_inc(v_value_1090_);
v_tail_1091_ = lean_ctor_get(v_x_1088_, 2);
lean_inc(v_tail_1091_);
lean_dec_ref_known(v_x_1088_, 3);
lean_inc(v_f_1086_);
v___x_1092_ = lean_apply_3(v_f_1086_, v_x_1087_, v_key_1089_, v_value_1090_);
v_x_1087_ = v___x_1092_;
v_x_1088_ = v_tail_1091_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1094_, lean_object* v_as_1095_, size_t v_i_1096_, size_t v_stop_1097_, lean_object* v_b_1098_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_usize_dec_eq(v_i_1096_, v_stop_1097_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; 
v___x_1100_ = lean_array_uget_borrowed(v_as_1095_, v_i_1096_);
lean_inc(v___x_1100_);
lean_inc(v_f_1094_);
v___x_1101_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1094_, v_b_1098_, v___x_1100_);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_i_1096_, v___x_1102_);
v_i_1096_ = v___x_1103_;
v_b_1098_ = v___x_1101_;
goto _start;
}
else
{
lean_dec(v_f_1094_);
return v_b_1098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1105_, lean_object* v_as_1106_, lean_object* v_i_1107_, lean_object* v_stop_1108_, lean_object* v_b_1109_){
_start:
{
size_t v_i_boxed_1110_; size_t v_stop_boxed_1111_; lean_object* v_res_1112_; 
v_i_boxed_1110_ = lean_unbox_usize(v_i_1107_);
lean_dec(v_i_1107_);
v_stop_boxed_1111_ = lean_unbox_usize(v_stop_1108_);
lean_dec(v_stop_1108_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1105_, v_as_1106_, v_i_boxed_1110_, v_stop_boxed_1111_, v_b_1109_);
lean_dec_ref(v_as_1106_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1113_, lean_object* v_init_1114_, lean_object* v_m_1115_){
_start:
{
lean_object* v_map_u2081_1116_; lean_object* v_map_u2082_1117_; lean_object* v_buckets_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_map_u2081_1116_ = lean_ctor_get(v_m_1115_, 0);
v_map_u2082_1117_ = lean_ctor_get(v_m_1115_, 1);
v_buckets_1118_ = lean_ctor_get(v_map_u2081_1116_, 1);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_array_get_size(v_buckets_1118_);
v___x_1121_ = lean_nat_dec_lt(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1117_, v_f_1113_, v_init_1114_);
return v___x_1122_;
}
else
{
size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = ((size_t)0ULL);
v___x_1124_ = lean_usize_of_nat(v___x_1120_);
lean_inc(v_f_1113_);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1113_, v_buckets_1118_, v___x_1123_, v___x_1124_, v_init_1114_);
v___x_1126_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1117_, v_f_1113_, v___x_1125_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1127_, lean_object* v_init_1128_, lean_object* v_m_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1127_, v_init_1128_, v_m_1129_);
lean_dec_ref(v_m_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1131_, lean_object* v_e_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v_toEnvExtension_1134_; lean_object* v_asyncMode_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1133_ = l_Lean_aliasExtension;
v_toEnvExtension_1134_ = lean_ctor_get(v___x_1133_, 0);
v_asyncMode_1135_ = lean_ctor_get(v_toEnvExtension_1134_, 2);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1136_, 0, v_e_1132_);
v___x_1137_ = lean_obj_once(&l_Lean_getAliasState___closed__0, &l_Lean_getAliasState___closed__0_once, _init_l_Lean_getAliasState___closed__0);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_box(0);
v___x_1140_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1137_, v___x_1133_, v_env_1131_, v_asyncMode_1135_, v___x_1139_);
v___x_1141_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1136_, v___x_1138_, v___x_1140_);
lean_dec(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1142_, lean_object* v_00_u03c3_1143_, lean_object* v_f_1144_, lean_object* v_init_1145_, lean_object* v_m_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1144_, v_init_1145_, v_m_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1148_, lean_object* v_00_u03c3_1149_, lean_object* v_f_1150_, lean_object* v_init_1151_, lean_object* v_m_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1148_, v_00_u03c3_1149_, v_f_1150_, v_init_1151_, v_m_1152_);
lean_dec_ref(v_m_1152_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1154_, lean_object* v_00_u03c3_1155_, lean_object* v_f_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1156_, v_x_1157_, v_x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_map_1162_, lean_object* v_f_1163_, lean_object* v_init_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1162_, v_f_1163_, v_init_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_map_1168_, lean_object* v_f_1169_, lean_object* v_init_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1166_, v_00_u03b2_1167_, v_map_1168_, v_f_1169_, v_init_1170_);
lean_dec_ref(v_map_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1172_, lean_object* v_00_u03c3_1173_, lean_object* v_f_1174_, lean_object* v_as_1175_, size_t v_i_1176_, size_t v_stop_1177_, lean_object* v_b_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1174_, v_as_1175_, v_i_1176_, v_stop_1177_, v_b_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1180_, lean_object* v_00_u03c3_1181_, lean_object* v_f_1182_, lean_object* v_as_1183_, lean_object* v_i_1184_, lean_object* v_stop_1185_, lean_object* v_b_1186_){
_start:
{
size_t v_i_boxed_1187_; size_t v_stop_boxed_1188_; lean_object* v_res_1189_; 
v_i_boxed_1187_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_stop_boxed_1188_ = lean_unbox_usize(v_stop_1185_);
lean_dec(v_stop_1185_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1180_, v_00_u03c3_1181_, v_f_1182_, v_as_1183_, v_i_boxed_1187_, v_stop_boxed_1188_, v_b_1186_);
lean_dec_ref(v_as_1183_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1190_, lean_object* v_f_1191_, lean_object* v_init_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1191_, v_map_1190_, v_init_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1194_, lean_object* v_f_1195_, lean_object* v_init_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1194_, v_f_1195_, v_init_1196_);
lean_dec_ref(v_map_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_map_1200_, lean_object* v_f_1201_, lean_object* v_init_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1201_, v_map_1200_, v_init_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_map_1206_, lean_object* v_f_1207_, lean_object* v_init_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1204_, v_00_u03b2_1205_, v_map_1206_, v_f_1207_, v_init_1208_);
lean_dec_ref(v_map_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1210_, lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_f_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1213_, v_x_1214_, v_x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1217_, lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_f_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1217_, v_00_u03b1_1218_, v_00_u03b2_1219_, v_f_1220_, v_x_1221_, v_x_1222_);
lean_dec_ref(v_x_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_00_u03c3_1226_, lean_object* v_f_1227_, lean_object* v_as_1228_, size_t v_i_1229_, size_t v_stop_1230_, lean_object* v_b_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1227_, v_as_1228_, v_i_1229_, v_stop_1230_, v_b_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_00_u03c3_1235_, lean_object* v_f_1236_, lean_object* v_as_1237_, lean_object* v_i_1238_, lean_object* v_stop_1239_, lean_object* v_b_1240_){
_start:
{
size_t v_i_boxed_1241_; size_t v_stop_boxed_1242_; lean_object* v_res_1243_; 
v_i_boxed_1241_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_stop_boxed_1242_ = lean_unbox_usize(v_stop_1239_);
lean_dec(v_stop_1239_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1233_, v_00_u03b2_1234_, v_00_u03c3_1235_, v_f_1236_, v_as_1237_, v_i_boxed_1241_, v_stop_boxed_1242_, v_b_1240_);
lean_dec_ref(v_as_1237_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1244_, lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_f_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_heq_1250_, lean_object* v_i_1251_, lean_object* v_acc_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1247_, v_keys_1248_, v_vals_1249_, v_i_1251_, v_acc_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1254_, lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_f_1257_, lean_object* v_keys_1258_, lean_object* v_vals_1259_, lean_object* v_heq_1260_, lean_object* v_i_1261_, lean_object* v_acc_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1254_, v_00_u03b1_1255_, v_00_u03b2_1256_, v_f_1257_, v_keys_1258_, v_vals_1259_, v_heq_1260_, v_i_1261_, v_acc_1262_);
lean_dec_ref(v_vals_1259_);
lean_dec_ref(v_keys_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1264_, uint8_t v_mayBeReserved_1265_, lean_object* v_declName_1266_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = l_Lean_Environment_containsOnBranch(v_env_1264_, v_declName_1266_);
if (v___x_1270_ == 0)
{
if (v_mayBeReserved_1265_ == 0)
{
goto v___jp_1267_;
}
else
{
uint8_t v___x_1271_; 
lean_inc(v_declName_1266_);
lean_inc_ref(v_env_1264_);
v___x_1271_ = lean_is_reserved_name(v_env_1264_, v_declName_1266_);
if (v___x_1271_ == 0)
{
goto v___jp_1267_;
}
else
{
lean_dec(v_declName_1266_);
lean_dec_ref(v_env_1264_);
return v___x_1271_;
}
}
}
else
{
lean_dec(v_declName_1266_);
lean_dec_ref(v_env_1264_);
return v___x_1270_;
}
v___jp_1267_:
{
uint8_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = 1;
v___x_1269_ = l_Lean_Environment_contains(v_env_1264_, v_declName_1266_, v___x_1268_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1272_, lean_object* v_mayBeReserved_1273_, lean_object* v_declName_1274_){
_start:
{
uint8_t v_mayBeReserved_boxed_1275_; uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_mayBeReserved_boxed_1275_ = lean_unbox(v_mayBeReserved_1273_);
v_res_1276_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1272_, v_mayBeReserved_boxed_1275_, v_declName_1274_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1278_, lean_object* v_decl_1279_, lean_object* v_ref_1280_){
_start:
{
lean_object* v_defValue_1282_; lean_object* v_descr_1283_; lean_object* v_deprecation_x3f_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_defValue_1282_ = lean_ctor_get(v_decl_1279_, 0);
v_descr_1283_ = lean_ctor_get(v_decl_1279_, 1);
v_deprecation_x3f_1284_ = lean_ctor_get(v_decl_1279_, 2);
v___x_1285_ = lean_alloc_ctor(1, 0, 1);
v___x_1286_ = lean_unbox(v_defValue_1282_);
lean_ctor_set_uint8(v___x_1285_, 0, v___x_1286_);
lean_inc(v_deprecation_x3f_1284_);
lean_inc_ref(v_descr_1283_);
lean_inc_n(v_name_1278_, 2);
v___x_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1287_, 0, v_name_1278_);
lean_ctor_set(v___x_1287_, 1, v_ref_1280_);
lean_ctor_set(v___x_1287_, 2, v___x_1285_);
lean_ctor_set(v___x_1287_, 3, v_descr_1283_);
lean_ctor_set(v___x_1287_, 4, v_deprecation_x3f_1284_);
v___x_1288_ = lean_register_option(v_name_1278_, v___x_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1296_; 
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v___x_1288_, 0);
lean_dec(v_unused_1297_);
v___x_1290_ = v___x_1288_;
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v___x_1288_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
lean_inc(v_defValue_1282_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_name_1278_);
lean_ctor_set(v___x_1292_, 1, v_defValue_1282_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_name_1278_);
v_a_1298_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1288_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1288_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1306_, lean_object* v_decl_1307_, lean_object* v_ref_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1306_, v_decl_1307_, v_ref_1308_);
lean_dec_ref(v_decl_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1329_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1330_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1331_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1328_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1353_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1354_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1355_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1352_, v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1357_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1358_, lean_object* v_opt_1359_){
_start:
{
lean_object* v_name_1360_; lean_object* v_defValue_1361_; lean_object* v_map_1362_; lean_object* v___x_1363_; 
v_name_1360_ = lean_ctor_get(v_opt_1359_, 0);
v_defValue_1361_ = lean_ctor_get(v_opt_1359_, 1);
v_map_1362_ = lean_ctor_get(v_opts_1358_, 0);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1362_, v_name_1360_);
if (lean_obj_tag(v___x_1363_) == 0)
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_unbox(v_defValue_1361_);
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; 
v_val_1365_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___x_1363_, 1);
if (lean_obj_tag(v_val_1365_) == 1)
{
uint8_t v_v_1366_; 
v_v_1366_ = lean_ctor_get_uint8(v_val_1365_, 0);
lean_dec_ref_known(v_val_1365_, 0);
return v_v_1366_;
}
else
{
uint8_t v___x_1367_; 
lean_dec(v_val_1365_);
v___x_1367_ = lean_unbox(v_defValue_1361_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1368_, lean_object* v_opt_1369_){
_start:
{
uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_res_1370_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1368_, v_opt_1369_);
lean_dec_ref(v_opt_1369_);
lean_dec_ref(v_opts_1368_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1375_, lean_object* v_env_1376_, uint8_t v_mayBeReserved_1377_, lean_object* v_as_1378_, size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_b_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_env_1376_);
lean_dec(v_declName_1375_);
lean_inc_ref(v_b_1381_);
return v_b_1381_;
}
else
{
lean_object* v_a_1383_; lean_object* v_toImport_1384_; lean_object* v_module_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_a_1383_ = lean_array_uget_borrowed(v_as_1378_, v_i_1380_);
v_toImport_1384_ = lean_ctor_get(v_a_1383_, 0);
v_module_1385_ = lean_ctor_get(v_toImport_1384_, 0);
v___x_1386_ = lean_box(0);
lean_inc(v_declName_1375_);
lean_inc(v_module_1385_);
v___x_1387_ = l_Lean_mkPrivateNameCore(v_module_1385_, v_declName_1375_);
lean_inc(v___x_1387_);
lean_inc_ref(v_env_1376_);
v___x_1388_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1376_, v_mayBeReserved_1377_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; 
lean_dec(v___x_1387_);
v___x_1389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_add(v_i_1380_, v___x_1390_);
v_i_1380_ = v___x_1391_;
v_b_1381_ = v___x_1389_;
goto _start;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_env_1376_);
lean_dec(v_declName_1375_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1387_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1386_);
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1396_, lean_object* v_env_1397_, lean_object* v_mayBeReserved_1398_, lean_object* v_as_1399_, lean_object* v_sz_1400_, lean_object* v_i_1401_, lean_object* v_b_1402_){
_start:
{
uint8_t v_mayBeReserved_boxed_1403_; size_t v_sz_boxed_1404_; size_t v_i_boxed_1405_; lean_object* v_res_1406_; 
v_mayBeReserved_boxed_1403_ = lean_unbox(v_mayBeReserved_1398_);
v_sz_boxed_1404_ = lean_unbox_usize(v_sz_1400_);
lean_dec(v_sz_1400_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1396_, v_env_1397_, v_mayBeReserved_boxed_1403_, v_as_1399_, v_sz_boxed_1404_, v_i_boxed_1405_, v_b_1402_);
lean_dec_ref(v_b_1402_);
lean_dec_ref(v_as_1399_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1407_, lean_object* v_opts_1408_, uint8_t v_mayBeReserved_1409_, lean_object* v_declName_1410_){
_start:
{
uint8_t v_isExporting_1426_; 
v_isExporting_1426_ = lean_ctor_get_uint8(v_env_1407_, sizeof(void*)*13);
if (v_isExporting_1426_ == 0)
{
goto v___jp_1411_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1428_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1408_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_env_1407_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
else
{
goto v___jp_1411_;
}
}
v___jp_1411_:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
lean_inc(v_declName_1410_);
v___x_1412_ = l_Lean_mkPrivateName(v_env_1407_, v_declName_1410_);
lean_inc(v___x_1412_);
lean_inc_ref(v_env_1407_);
v___x_1413_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1407_, v_mayBeReserved_1409_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; uint8_t v_isModule_1415_; 
lean_dec(v___x_1412_);
v___x_1414_ = l_Lean_Environment_header(v_env_1407_);
v_isModule_1415_ = lean_ctor_get_uint8(v___x_1414_, sizeof(void*)*8 + 4);
if (v_isModule_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec_ref(v___x_1414_);
lean_dec(v_declName_1410_);
lean_dec_ref(v_env_1407_);
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
else
{
lean_object* v_importAllModules_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v_fst_1423_; 
v_importAllModules_1417_ = lean_ctor_get(v___x_1414_, 6);
lean_inc_ref(v_importAllModules_1417_);
lean_dec_ref(v___x_1414_);
v___x_1418_ = lean_box(0);
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1420_ = lean_array_size(v_importAllModules_1417_);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1410_, v_env_1407_, v_mayBeReserved_1409_, v_importAllModules_1417_, v_sz_1420_, v___x_1421_, v___x_1419_);
lean_dec_ref(v_importAllModules_1417_);
v_fst_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_fst_1423_);
lean_dec_ref(v___x_1422_);
if (lean_obj_tag(v_fst_1423_) == 0)
{
return v___x_1418_;
}
else
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v_fst_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v_fst_1423_, 1);
return v_val_1424_;
}
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_env_1407_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1412_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1430_, lean_object* v_opts_1431_, lean_object* v_mayBeReserved_1432_, lean_object* v_declName_1433_){
_start:
{
uint8_t v_mayBeReserved_boxed_1434_; lean_object* v_res_1435_; 
v_mayBeReserved_boxed_1434_ = lean_unbox(v_mayBeReserved_1432_);
v_res_1435_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1430_, v_opts_1431_, v_mayBeReserved_boxed_1434_, v_declName_1433_);
lean_dec_ref(v_opts_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1436_, lean_object* v_opts_1437_, uint8_t v_mayBeReserved_1438_, lean_object* v_ns_1439_, lean_object* v_id_1440_){
_start:
{
lean_object* v_resolvedId_1441_; uint8_t v___x_1442_; lean_object* v_resolvedIds_1443_; 
lean_inc(v_id_1440_);
v_resolvedId_1441_ = l_Lean_Name_append(v_ns_1439_, v_id_1440_);
v___x_1442_ = l_Lean_Name_isAtomic(v_id_1440_);
lean_dec(v_id_1440_);
lean_inc_ref(v_env_1436_);
v_resolvedIds_1443_ = l_Lean_getAliases(v_env_1436_, v_resolvedId_1441_, v___x_1442_);
if (v___x_1442_ == 0)
{
goto v___jp_1444_;
}
else
{
uint8_t v___x_1450_; 
lean_inc(v_resolvedId_1441_);
lean_inc_ref(v_env_1436_);
v___x_1450_ = l_Lean_isProtected(v_env_1436_, v_resolvedId_1441_);
if (v___x_1450_ == 0)
{
goto v___jp_1444_;
}
else
{
lean_dec(v_resolvedId_1441_);
lean_dec_ref(v_env_1436_);
return v_resolvedIds_1443_;
}
}
v___jp_1444_:
{
uint8_t v___x_1445_; 
lean_inc(v_resolvedId_1441_);
lean_inc_ref(v_env_1436_);
v___x_1445_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1436_, v_mayBeReserved_1438_, v_resolvedId_1441_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1436_, v_opts_1437_, v_mayBeReserved_1438_, v_resolvedId_1441_);
if (lean_obj_tag(v___x_1446_) == 1)
{
lean_object* v_val_1447_; lean_object* v___x_1448_; 
v_val_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_val_1447_);
lean_ctor_set(v___x_1448_, 1, v_resolvedIds_1443_);
return v___x_1448_;
}
else
{
lean_dec(v___x_1446_);
return v_resolvedIds_1443_;
}
}
else
{
lean_object* v___x_1449_; 
lean_dec_ref(v_env_1436_);
v___x_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_resolvedId_1441_);
lean_ctor_set(v___x_1449_, 1, v_resolvedIds_1443_);
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1451_, lean_object* v_opts_1452_, lean_object* v_mayBeReserved_1453_, lean_object* v_ns_1454_, lean_object* v_id_1455_){
_start:
{
uint8_t v_mayBeReserved_boxed_1456_; lean_object* v_res_1457_; 
v_mayBeReserved_boxed_1456_ = lean_unbox(v_mayBeReserved_1453_);
v_res_1457_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1451_, v_opts_1452_, v_mayBeReserved_boxed_1456_, v_ns_1454_, v_id_1455_);
lean_dec_ref(v_opts_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1458_, lean_object* v_opts_1459_, uint8_t v_mayBeReserved_1460_, lean_object* v_id_1461_, lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 1)
{
lean_object* v_pre_1463_; lean_object* v___x_1464_; 
v_pre_1463_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_pre_1463_);
lean_inc(v_id_1461_);
lean_inc_ref(v_env_1458_);
v___x_1464_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1458_, v_opts_1459_, v_mayBeReserved_1460_, v_x_1462_, v_id_1461_);
if (lean_obj_tag(v___x_1464_) == 0)
{
v_x_1462_ = v_pre_1463_;
goto _start;
}
else
{
lean_dec(v_pre_1463_);
lean_dec(v_id_1461_);
lean_dec_ref(v_env_1458_);
return v___x_1464_;
}
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_x_1462_);
lean_dec(v_id_1461_);
lean_dec_ref(v_env_1458_);
v___x_1466_ = lean_box(0);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1467_, lean_object* v_opts_1468_, lean_object* v_mayBeReserved_1469_, lean_object* v_id_1470_, lean_object* v_x_1471_){
_start:
{
uint8_t v_mayBeReserved_boxed_1472_; lean_object* v_res_1473_; 
v_mayBeReserved_boxed_1472_ = lean_unbox(v_mayBeReserved_1469_);
v_res_1473_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1467_, v_opts_1468_, v_mayBeReserved_boxed_1472_, v_id_1470_, v_x_1471_);
lean_dec_ref(v_opts_1468_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1474_, lean_object* v_opts_1475_, uint8_t v_mayBeReserved_1476_, lean_object* v_id_1477_){
_start:
{
uint8_t v___x_1478_; 
v___x_1478_ = l_Lean_Name_isAtomic(v_id_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_resolvedId_1481_; uint8_t v___x_1482_; 
v___x_1479_ = l_Lean_rootNamespace;
v___x_1480_ = lean_box(0);
v_resolvedId_1481_ = l_Lean_Name_replacePrefix(v_id_1477_, v___x_1479_, v___x_1480_);
lean_inc(v_resolvedId_1481_);
lean_inc_ref(v_env_1474_);
v___x_1482_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1474_, v_mayBeReserved_1476_, v_resolvedId_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1474_, v_opts_1475_, v_mayBeReserved_1476_, v_resolvedId_1481_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; 
lean_dec_ref(v_env_1474_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v_resolvedId_1481_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1485_; 
lean_dec(v_id_1477_);
lean_dec_ref(v_env_1474_);
v___x_1485_ = lean_box(0);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1486_, lean_object* v_opts_1487_, lean_object* v_mayBeReserved_1488_, lean_object* v_id_1489_){
_start:
{
uint8_t v_mayBeReserved_boxed_1490_; lean_object* v_res_1491_; 
v_mayBeReserved_boxed_1490_ = lean_unbox(v_mayBeReserved_1488_);
v_res_1491_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1486_, v_opts_1487_, v_mayBeReserved_boxed_1490_, v_id_1489_);
lean_dec_ref(v_opts_1487_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1492_, lean_object* v_opts_1493_, uint8_t v_mayBeReserved_1494_, lean_object* v_id_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 0)
{
lean_dec(v_id_1495_);
lean_dec_ref(v_env_1492_);
return v_x_1497_;
}
else
{
lean_object* v_head_1498_; 
v_head_1498_ = lean_ctor_get(v_x_1496_, 0);
lean_inc(v_head_1498_);
if (lean_obj_tag(v_head_1498_) == 0)
{
lean_object* v_tail_1499_; lean_object* v_ns_1500_; lean_object* v_except_1501_; uint8_t v___x_1502_; 
v_tail_1499_ = lean_ctor_get(v_x_1496_, 1);
lean_inc(v_tail_1499_);
lean_dec_ref_known(v_x_1496_, 2);
v_ns_1500_ = lean_ctor_get(v_head_1498_, 0);
lean_inc(v_ns_1500_);
v_except_1501_ = lean_ctor_get(v_head_1498_, 1);
lean_inc(v_except_1501_);
lean_dec_ref_known(v_head_1498_, 2);
v___x_1502_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1495_, v_except_1501_);
lean_dec(v_except_1501_);
if (v___x_1502_ == 0)
{
lean_object* v_newResolvedIds_1503_; lean_object* v___x_1504_; 
lean_inc(v_id_1495_);
lean_inc_ref(v_env_1492_);
v_newResolvedIds_1503_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1492_, v_opts_1493_, v_mayBeReserved_1494_, v_ns_1500_, v_id_1495_);
v___x_1504_ = l_List_appendTR___redArg(v_newResolvedIds_1503_, v_x_1497_);
v_x_1496_ = v_tail_1499_;
v_x_1497_ = v___x_1504_;
goto _start;
}
else
{
lean_dec(v_ns_1500_);
v_x_1496_ = v_tail_1499_;
goto _start;
}
}
else
{
lean_object* v_tail_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1527_; 
v_tail_1507_ = lean_ctor_get(v_x_1496_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_x_1496_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_x_1496_, 0);
lean_dec(v_unused_1528_);
v___x_1509_ = v_x_1496_;
v_isShared_1510_ = v_isSharedCheck_1527_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_tail_1507_);
lean_dec(v_x_1496_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1527_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_id_1511_; lean_object* v_declName_1512_; uint8_t v___x_1513_; 
v_id_1511_ = lean_ctor_get(v_head_1498_, 0);
lean_inc(v_id_1511_);
v_declName_1512_ = lean_ctor_get(v_head_1498_, 1);
lean_inc(v_declName_1512_);
lean_dec_ref_known(v_head_1498_, 2);
v___x_1513_ = lean_name_eq(v_id_1511_, v_id_1495_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Lean_Name_isPrefixOf(v_id_1511_, v_id_1495_);
if (v___x_1514_ == 0)
{
lean_dec(v_declName_1512_);
lean_dec(v_id_1511_);
lean_del_object(v___x_1509_);
v_x_1496_ = v_tail_1507_;
goto _start;
}
else
{
lean_object* v_candidate_1516_; uint8_t v___x_1517_; 
lean_inc(v_id_1495_);
v_candidate_1516_ = l_Lean_Name_replacePrefix(v_id_1495_, v_id_1511_, v_declName_1512_);
lean_dec(v_declName_1512_);
lean_dec(v_id_1511_);
lean_inc(v_candidate_1516_);
lean_inc_ref(v_env_1492_);
v___x_1517_ = l_Lean_Environment_contains(v_env_1492_, v_candidate_1516_, v___x_1514_);
if (v___x_1517_ == 0)
{
lean_dec(v_candidate_1516_);
lean_del_object(v___x_1509_);
v_x_1496_ = v_tail_1507_;
goto _start;
}
else
{
lean_object* v___x_1520_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_x_1497_);
lean_ctor_set(v___x_1509_, 0, v_candidate_1516_);
v___x_1520_ = v___x_1509_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_candidate_1516_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_x_1497_);
v___x_1520_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
v_x_1496_ = v_tail_1507_;
v_x_1497_ = v___x_1520_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1524_; 
lean_dec(v_id_1511_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_x_1497_);
lean_ctor_set(v___x_1509_, 0, v_declName_1512_);
v___x_1524_ = v___x_1509_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_declName_1512_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_x_1497_);
v___x_1524_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v_x_1496_ = v_tail_1507_;
v_x_1497_ = v___x_1524_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1529_, lean_object* v_opts_1530_, lean_object* v_mayBeReserved_1531_, lean_object* v_id_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
uint8_t v_mayBeReserved_boxed_1535_; lean_object* v_res_1536_; 
v_mayBeReserved_boxed_1535_ = lean_unbox(v_mayBeReserved_1531_);
v_res_1536_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1529_, v_opts_1530_, v_mayBeReserved_boxed_1535_, v_id_1532_, v_x_1533_, v_x_1534_);
lean_dec_ref(v_opts_1530_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1538_){
_start:
{
lean_object* v___f_1539_; lean_object* v___x_1540_; 
v___f_1539_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1540_ = l_List_eraseDupsBy___redArg(v___f_1539_, v_as_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
if (lean_obj_tag(v_a_1542_) == 0)
{
lean_object* v___x_1544_; 
lean_dec(v_projs_1541_);
v___x_1544_ = l_List_reverse___redArg(v_a_1543_);
return v___x_1544_;
}
else
{
lean_object* v_head_1545_; lean_object* v_tail_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1555_; 
v_head_1545_ = lean_ctor_get(v_a_1542_, 0);
v_tail_1546_ = lean_ctor_get(v_a_1542_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_a_1542_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1548_ = v_a_1542_;
v_isShared_1549_ = v_isSharedCheck_1555_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_tail_1546_);
lean_inc(v_head_1545_);
lean_dec(v_a_1542_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1555_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_inc(v_projs_1541_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_head_1545_);
lean_ctor_set(v___x_1550_, 1, v_projs_1541_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 1, v_a_1543_);
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_a_1543_);
v___x_1552_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
v_a_1542_ = v_tail_1546_;
v_a_1543_ = v___x_1552_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1556_, lean_object* v_opts_1557_, lean_object* v_ns_1558_, lean_object* v_openDecls_1559_, lean_object* v_extractionResult_1560_, lean_object* v_id_1561_, lean_object* v_projs_1562_){
_start:
{
if (lean_obj_tag(v_id_1561_) == 1)
{
lean_object* v_pre_1563_; lean_object* v_str_1564_; lean_object* v_imported_1565_; lean_object* v_ctx_1566_; lean_object* v_scopes_1567_; lean_object* v___x_1568_; lean_object* v_id_1569_; uint8_t v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1585_; uint8_t v___y_1591_; 
v_pre_1563_ = lean_ctor_get(v_id_1561_, 0);
lean_inc(v_pre_1563_);
v_str_1564_ = lean_ctor_get(v_id_1561_, 1);
lean_inc_ref(v_str_1564_);
v_imported_1565_ = lean_ctor_get(v_extractionResult_1560_, 1);
v_ctx_1566_ = lean_ctor_get(v_extractionResult_1560_, 2);
v_scopes_1567_ = lean_ctor_get(v_extractionResult_1560_, 3);
lean_inc(v_scopes_1567_);
lean_inc(v_ctx_1566_);
lean_inc(v_imported_1565_);
v___x_1568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1568_, 0, v_id_1561_);
lean_ctor_set(v___x_1568_, 1, v_imported_1565_);
lean_ctor_set(v___x_1568_, 2, v_ctx_1566_);
lean_ctor_set(v___x_1568_, 3, v_scopes_1567_);
v_id_1569_ = l_Lean_MacroScopesView_review(v___x_1568_);
if (lean_obj_tag(v_id_1569_) == 1)
{
lean_object* v_str_1603_; uint8_t v___x_1604_; 
v_str_1603_ = lean_ctor_get(v_id_1569_, 1);
lean_inc_ref(v_str_1603_);
lean_inc_ref(v_env_1556_);
v___x_1604_ = l_Lean_isReservedNameCandidate(v_env_1556_, v_str_1603_);
v___y_1591_ = v___x_1604_;
goto v___jp_1590_;
}
else
{
uint8_t v___x_1605_; 
v___x_1605_ = 0;
v___y_1591_ = v___x_1605_;
goto v___jp_1590_;
}
v___jp_1570_:
{
lean_object* v_resolvedIds_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v_resolvedIds_1576_; 
lean_inc(v_openDecls_1559_);
lean_inc(v_id_1569_);
lean_inc_ref_n(v_env_1556_, 2);
v_resolvedIds_1573_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1556_, v_opts_1557_, v___y_1571_, v_id_1569_, v_openDecls_1559_, v___y_1572_);
v___x_1574_ = l_Lean_Name_isAtomic(v_id_1569_);
v___x_1575_ = l_Lean_getAliases(v_env_1556_, v_id_1569_, v___x_1574_);
lean_dec(v_id_1569_);
v_resolvedIds_1576_ = l_List_appendTR___redArg(v___x_1575_, v_resolvedIds_1573_);
if (lean_obj_tag(v_resolvedIds_1576_) == 0)
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_str_1564_);
lean_ctor_set(v___x_1577_, 1, v_projs_1562_);
v_id_1561_ = v_pre_1563_;
v_projs_1562_ = v___x_1577_;
goto _start;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_str_1564_);
lean_dec(v_pre_1563_);
lean_dec(v_openDecls_1559_);
lean_dec(v_ns_1558_);
lean_dec_ref(v_env_1556_);
v___x_1579_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1576_);
v___x_1580_ = lean_box(0);
v___x_1581_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1562_, v___x_1579_, v___x_1580_);
return v___x_1581_;
}
}
v___jp_1582_:
{
lean_object* v___x_1586_; 
lean_inc(v_id_1569_);
lean_inc_ref(v_env_1556_);
v___x_1586_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1556_, v_opts_1557_, v___y_1584_, v_id_1569_);
if (lean_obj_tag(v___x_1586_) == 1)
{
lean_object* v_val_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_val_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_val_1587_);
lean_ctor_set(v___x_1588_, 1, v___y_1583_);
v___x_1589_ = l_List_appendTR___redArg(v___x_1588_, v___y_1585_);
v___y_1571_ = v___y_1584_;
v___y_1572_ = v___x_1589_;
goto v___jp_1570_;
}
else
{
lean_dec(v___x_1586_);
lean_dec(v___y_1583_);
v___y_1571_ = v___y_1584_;
v___y_1572_ = v___y_1585_;
goto v___jp_1570_;
}
}
v___jp_1590_:
{
lean_object* v___x_1592_; 
lean_inc(v_ns_1558_);
lean_inc(v_id_1569_);
lean_inc_ref(v_env_1556_);
v___x_1592_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1556_, v_opts_1557_, v___y_1591_, v_id_1569_, v_ns_1558_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; 
lean_inc(v_id_1569_);
lean_inc_ref(v_env_1556_);
v___x_1593_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1556_, v_opts_1557_, v___y_1591_, v_id_1569_);
if (lean_obj_tag(v___x_1593_) == 0)
{
uint8_t v___x_1594_; 
lean_inc(v_id_1569_);
lean_inc_ref(v_env_1556_);
v___x_1594_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1556_, v___y_1591_, v_id_1569_);
if (v___x_1594_ == 0)
{
v___y_1583_ = v___x_1592_;
v___y_1584_ = v___y_1591_;
v___y_1585_ = v___x_1592_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1595_; 
lean_inc(v_id_1569_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_id_1569_);
lean_ctor_set(v___x_1595_, 1, v___x_1592_);
v___y_1583_ = v___x_1592_;
v___y_1584_ = v___y_1591_;
v___y_1585_ = v___x_1595_;
goto v___jp_1582_;
}
}
else
{
lean_object* v_val_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_id_1569_);
lean_dec_ref(v_str_1564_);
lean_dec(v_pre_1563_);
lean_dec(v_openDecls_1559_);
lean_dec(v_ns_1558_);
lean_dec_ref(v_env_1556_);
v_val_1596_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_val_1596_);
lean_ctor_set(v___x_1597_, 1, v_projs_1562_);
v___x_1598_ = lean_box(0);
v___x_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
return v___x_1599_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec(v_id_1569_);
lean_dec_ref(v_str_1564_);
lean_dec(v_pre_1563_);
lean_dec(v_openDecls_1559_);
lean_dec(v_ns_1558_);
lean_dec_ref(v_env_1556_);
v___x_1600_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1592_);
v___x_1601_ = lean_box(0);
v___x_1602_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1562_, v___x_1600_, v___x_1601_);
return v___x_1602_;
}
}
}
else
{
lean_object* v___x_1606_; 
lean_dec(v_projs_1562_);
lean_dec(v_id_1561_);
lean_dec(v_openDecls_1559_);
lean_dec(v_ns_1558_);
lean_dec_ref(v_env_1556_);
v___x_1606_ = lean_box(0);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1607_, lean_object* v_opts_1608_, lean_object* v_ns_1609_, lean_object* v_openDecls_1610_, lean_object* v_extractionResult_1611_, lean_object* v_id_1612_, lean_object* v_projs_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1607_, v_opts_1608_, v_ns_1609_, v_openDecls_1610_, v_extractionResult_1611_, v_id_1612_, v_projs_1613_);
lean_dec_ref(v_extractionResult_1611_);
lean_dec_ref(v_opts_1608_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1615_, lean_object* v_opts_1616_, lean_object* v_ns_1617_, lean_object* v_openDecls_1618_, lean_object* v_id_1619_){
_start:
{
lean_object* v_extractionResult_1620_; lean_object* v_name_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_extractionResult_1620_ = l_Lean_extractMacroScopes(v_id_1619_);
v_name_1621_ = lean_ctor_get(v_extractionResult_1620_, 0);
lean_inc(v_name_1621_);
v___x_1622_ = lean_box(0);
v___x_1623_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1615_, v_opts_1616_, v_ns_1617_, v_openDecls_1618_, v_extractionResult_1620_, v_name_1621_, v___x_1622_);
lean_dec_ref(v_extractionResult_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1624_, lean_object* v_opts_1625_, lean_object* v_ns_1626_, lean_object* v_openDecls_1627_, lean_object* v_id_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_ResolveName_resolveGlobalName(v_env_1624_, v_opts_1625_, v_ns_1626_, v_openDecls_1627_, v_id_1628_);
lean_dec_ref(v_opts_1625_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_panic_fn_borrowed(v___x_1631_, v_msg_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1636_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1637_ = lean_unsigned_to_nat(9u);
v___x_1638_ = lean_unsigned_to_nat(257u);
v___x_1639_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1640_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1641_ = l_mkPanicMessageWithDecl(v___x_1640_, v___x_1639_, v___x_1638_, v___x_1637_, v___x_1636_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1642_, lean_object* v_n_1643_, lean_object* v_ns_1644_){
_start:
{
switch(lean_obj_tag(v_ns_1644_))
{
case 1:
{
lean_object* v_pre_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_pre_1645_ = lean_ctor_get(v_ns_1644_, 0);
lean_inc(v_pre_1645_);
lean_inc(v_n_1643_);
v___x_1646_ = l_Lean_Name_append(v_ns_1644_, v_n_1643_);
lean_inc_ref(v_env_1642_);
v___x_1647_ = l_Lean_Environment_isNamespace(v_env_1642_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_dec(v___x_1646_);
v_ns_1644_ = v_pre_1645_;
goto _start;
}
else
{
lean_object* v___x_1649_; 
lean_dec(v_pre_1645_);
lean_dec(v_n_1643_);
lean_dec_ref(v_env_1642_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
return v___x_1649_;
}
}
case 0:
{
lean_object* v___x_1650_; lean_object* v_n_1651_; uint8_t v___x_1652_; 
v___x_1650_ = l_Lean_rootNamespace;
v_n_1651_ = l_Lean_Name_replacePrefix(v_n_1643_, v___x_1650_, v_ns_1644_);
v___x_1652_ = l_Lean_Environment_isNamespace(v_env_1642_, v_n_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec(v_n_1651_);
v___x_1653_ = lean_box(0);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_n_1651_);
return v___x_1654_;
}
}
default: 
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec(v_ns_1644_);
lean_dec(v_n_1643_);
lean_dec_ref(v_env_1642_);
v___x_1655_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1656_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1655_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1657_, lean_object* v_n_1658_, lean_object* v_x_1659_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v___x_1660_; 
lean_dec(v_n_1658_);
lean_dec_ref(v_env_1657_);
v___x_1660_ = lean_box(0);
return v___x_1660_;
}
else
{
lean_object* v_head_1661_; 
v_head_1661_ = lean_ctor_get(v_x_1659_, 0);
if (lean_obj_tag(v_head_1661_) == 0)
{
lean_object* v_tail_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1677_; 
lean_inc_ref(v_head_1661_);
v_tail_1662_ = lean_ctor_get(v_x_1659_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1659_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_x_1659_, 0);
lean_dec(v_unused_1678_);
v___x_1664_ = v_x_1659_;
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_tail_1662_);
lean_dec(v_x_1659_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_ns_1666_; lean_object* v_except_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_ns_1666_ = lean_ctor_get(v_head_1661_, 0);
lean_inc(v_ns_1666_);
v_except_1667_ = lean_ctor_get(v_head_1661_, 1);
lean_inc(v_except_1667_);
lean_dec_ref_known(v_head_1661_, 2);
lean_inc(v_n_1658_);
v___x_1668_ = l_Lean_Name_append(v_ns_1666_, v_n_1658_);
lean_inc_ref(v_env_1657_);
v___x_1669_ = l_Lean_Environment_isNamespace(v_env_1657_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec(v___x_1668_);
lean_dec(v_except_1667_);
lean_del_object(v___x_1664_);
v_x_1659_ = v_tail_1662_;
goto _start;
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1658_, v_except_1667_);
lean_dec(v_except_1667_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1657_, v_n_1658_, v_tail_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1672_);
lean_ctor_set(v___x_1664_, 0, v___x_1668_);
v___x_1674_ = v___x_1664_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
lean_dec(v___x_1668_);
lean_del_object(v___x_1664_);
v_x_1659_ = v_tail_1662_;
goto _start;
}
}
}
}
else
{
lean_object* v_tail_1679_; 
v_tail_1679_ = lean_ctor_get(v_x_1659_, 1);
lean_inc(v_tail_1679_);
lean_dec_ref_known(v_x_1659_, 2);
v_x_1659_ = v_tail_1679_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1681_, lean_object* v_ns_1682_, lean_object* v_openDecls_1683_, lean_object* v_id_1684_){
_start:
{
lean_object* v___x_1685_; 
lean_inc(v_id_1684_);
lean_inc_ref(v_env_1681_);
v___x_1685_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1681_, v_id_1684_, v_ns_1682_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1681_, v_id_1684_, v_openDecls_1683_);
return v___x_1686_;
}
else
{
lean_object* v_val_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_val_1687_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_val_1687_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1688_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1681_, v_id_1684_, v_openDecls_1683_);
v___x_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_val_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1690_, lean_object* v_inst_1691_){
_start:
{
lean_object* v_getCurrNamespace_1692_; lean_object* v_getOpenDecls_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1702_; 
v_getCurrNamespace_1692_ = lean_ctor_get(v_inst_1691_, 0);
v_getOpenDecls_1693_ = lean_ctor_get(v_inst_1691_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_inst_1691_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1695_ = v_inst_1691_;
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_getOpenDecls_1693_);
lean_inc(v_getCurrNamespace_1692_);
lean_dec(v_inst_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_inc(v_inst_1690_);
v___x_1697_ = lean_apply_2(v_inst_1690_, lean_box(0), v_getCurrNamespace_1692_);
v___x_1698_ = lean_apply_2(v_inst_1690_, lean_box(0), v_getOpenDecls_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 1, v___x_1698_);
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1703_, lean_object* v_n_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1705_, v_inst_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1714_, lean_object* v_toPure_1715_, lean_object* v_id_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, uint8_t v_____do__lift_1721_){
_start:
{
uint8_t v_isExporting_1725_; 
v_isExporting_1725_ = lean_ctor_get_uint8(v_____do__lift_1714_, sizeof(void*)*13);
if (v_isExporting_1725_ == 0)
{
lean_dec_ref(v_inst_1720_);
lean_dec(v_inst_1719_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_inst_1717_);
lean_dec(v_id_1716_);
goto v___jp_1722_;
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = l_Lean_isPrivateName(v_id_1716_);
if (v___x_1726_ == 0)
{
lean_dec_ref(v_inst_1720_);
lean_dec(v_inst_1719_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_inst_1717_);
lean_dec(v_id_1716_);
goto v___jp_1722_;
}
else
{
if (v_____do__lift_1721_ == 0)
{
lean_dec_ref(v_inst_1720_);
lean_dec(v_inst_1719_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_inst_1717_);
lean_dec(v_id_1716_);
goto v___jp_1722_;
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_toPure_1715_);
v___x_1727_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1728_ = 0;
v___x_1729_ = l_Lean_MessageData_ofConstName(v_id_1716_, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1727_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_logWarning___redArg(v_inst_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v___x_1732_);
return v___x_1733_;
}
}
}
v___jp_1722_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_apply_2(v_toPure_1715_, lean_box(0), v___x_1723_);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1734_, lean_object* v_toPure_1735_, lean_object* v_id_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_____do__lift_1741_){
_start:
{
uint8_t v_____do__lift_199__boxed_1742_; lean_object* v_res_1743_; 
v_____do__lift_199__boxed_1742_ = lean_unbox(v_____do__lift_1741_);
v_res_1743_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1734_, v_toPure_1735_, v_id_1736_, v_inst_1737_, v_inst_1738_, v_inst_1739_, v_inst_1740_, v_____do__lift_199__boxed_1742_);
lean_dec_ref(v_____do__lift_1734_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1744_, lean_object* v_id_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v___x_1750_, lean_object* v_toBind_1751_, lean_object* v_____do__lift_1752_){
_start:
{
lean_object* v___f_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_inc_ref(v_inst_1749_);
lean_inc_ref(v_inst_1746_);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1753_, 0, v_____do__lift_1752_);
lean_closure_set(v___f_1753_, 1, v_toPure_1744_);
lean_closure_set(v___f_1753_, 2, v_id_1745_);
lean_closure_set(v___f_1753_, 3, v_inst_1746_);
lean_closure_set(v___f_1753_, 4, v_inst_1747_);
lean_closure_set(v___f_1753_, 5, v_inst_1748_);
lean_closure_set(v___f_1753_, 6, v_inst_1749_);
v___x_1754_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1755_ = l_Lean_Option_getM___redArg(v_inst_1746_, v_inst_1749_, v___x_1750_, v___x_1754_);
v___x_1756_ = lean_apply_4(v_toBind_1751_, lean_box(0), lean_box(0), v___x_1755_, v___f_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_id_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v_toApplicative_1764_; lean_object* v_toBind_1765_; lean_object* v_getEnv_1766_; lean_object* v_toPure_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; 
v___x_1763_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1764_ = lean_ctor_get(v_inst_1757_, 0);
v_toBind_1765_ = lean_ctor_get(v_inst_1757_, 1);
lean_inc_n(v_toBind_1765_, 2);
v_getEnv_1766_ = lean_ctor_get(v_inst_1758_, 0);
lean_inc(v_getEnv_1766_);
lean_dec_ref(v_inst_1758_);
v_toPure_1767_ = lean_ctor_get(v_toApplicative_1764_, 1);
lean_inc(v_toPure_1767_);
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1768_, 0, v_toPure_1767_);
lean_closure_set(v___f_1768_, 1, v_id_1762_);
lean_closure_set(v___f_1768_, 2, v_inst_1757_);
lean_closure_set(v___f_1768_, 3, v_inst_1760_);
lean_closure_set(v___f_1768_, 4, v_inst_1761_);
lean_closure_set(v___f_1768_, 5, v_inst_1759_);
lean_closure_set(v___f_1768_, 6, v___x_1763_);
lean_closure_set(v___f_1768_, 7, v_toBind_1765_);
v___x_1769_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v_getEnv_1766_, v___f_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_id_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1771_, v_inst_1772_, v_inst_1773_, v_inst_1774_, v_inst_1775_, v_id_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1778_, lean_object* v_n_1779_, lean_object* v_toPure_1780_, uint8_t v___y_1781_, uint8_t v___x_1782_, lean_object* v_____r_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1778_, v_n_1779_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_box(v___y_1781_);
v___x_1786_ = lean_apply_2(v_toPure_1780_, lean_box(0), v___x_1785_);
return v___x_1786_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1788_; uint8_t v_isModule_1789_; 
v_val_1787_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1788_ = l_Lean_Environment_header(v_env_1778_);
v_isModule_1789_ = lean_ctor_get_uint8(v___x_1788_, sizeof(void*)*8 + 4);
if (v_isModule_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec_ref(v___x_1788_);
lean_dec(v_val_1787_);
v___x_1790_ = lean_box(v___x_1782_);
v___x_1791_ = lean_apply_2(v_toPure_1780_, lean_box(0), v___x_1790_);
return v___x_1791_;
}
else
{
lean_object* v_modules_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_modules_1792_ = lean_ctor_get(v___x_1788_, 3);
lean_inc_ref(v_modules_1792_);
lean_dec_ref(v___x_1788_);
v___x_1793_ = lean_array_get_size(v_modules_1792_);
v___x_1794_ = lean_nat_dec_lt(v_val_1787_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec_ref(v_modules_1792_);
lean_dec(v_val_1787_);
v___x_1795_ = lean_box(v_isModule_1789_);
v___x_1796_ = lean_apply_2(v_toPure_1780_, lean_box(0), v___x_1795_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v_toImport_1798_; uint8_t v_importAll_1799_; 
v___x_1797_ = lean_array_fget(v_modules_1792_, v_val_1787_);
lean_dec(v_val_1787_);
lean_dec_ref(v_modules_1792_);
v_toImport_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc_ref(v_toImport_1798_);
lean_dec(v___x_1797_);
v_importAll_1799_ = lean_ctor_get_uint8(v_toImport_1798_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1798_);
if (v_importAll_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_box(v_isModule_1789_);
v___x_1801_ = lean_apply_2(v_toPure_1780_, lean_box(0), v___x_1800_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_box(v___y_1781_);
v___x_1803_ = lean_apply_2(v_toPure_1780_, lean_box(0), v___x_1802_);
return v___x_1803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1804_, lean_object* v_n_1805_, lean_object* v_toPure_1806_, lean_object* v___y_1807_, lean_object* v___x_1808_, lean_object* v_____r_1809_){
_start:
{
uint8_t v___y_386__boxed_1810_; uint8_t v___x_387__boxed_1811_; lean_object* v_res_1812_; 
v___y_386__boxed_1810_ = lean_unbox(v___y_1807_);
v___x_387__boxed_1811_ = lean_unbox(v___x_1808_);
v_res_1812_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1804_, v_n_1805_, v_toPure_1806_, v___y_386__boxed_1810_, v___x_387__boxed_1811_, v_____r_1809_);
lean_dec(v_n_1805_);
lean_dec_ref(v_env_1804_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1813_, lean_object* v_n_1814_, lean_object* v_toPure_1815_, uint8_t v___x_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_toBind_1822_, uint8_t v___y_1823_, uint8_t v_____do__lift_1824_){
_start:
{
uint8_t v___y_1826_; uint8_t v_isExporting_1832_; 
v_isExporting_1832_ = lean_ctor_get_uint8(v_env_1813_, sizeof(void*)*13);
if (v_isExporting_1832_ == 0)
{
v___y_1826_ = v___y_1823_;
goto v___jp_1825_;
}
else
{
if (v_____do__lift_1824_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v_toBind_1822_);
lean_dec(v_inst_1821_);
lean_dec_ref(v_inst_1820_);
lean_dec_ref(v_inst_1819_);
lean_dec_ref(v_inst_1818_);
lean_dec_ref(v_inst_1817_);
lean_dec(v_n_1814_);
lean_dec_ref(v_env_1813_);
v___x_1833_ = lean_box(v___x_1816_);
v___x_1834_ = lean_apply_2(v_toPure_1815_, lean_box(0), v___x_1833_);
return v___x_1834_;
}
else
{
v___y_1826_ = v___y_1823_;
goto v___jp_1825_;
}
}
v___jp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1827_ = lean_box(v___y_1826_);
v___x_1828_ = lean_box(v___x_1816_);
lean_inc(v_n_1814_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1829_, 0, v_env_1813_);
lean_closure_set(v___f_1829_, 1, v_n_1814_);
lean_closure_set(v___f_1829_, 2, v_toPure_1815_);
lean_closure_set(v___f_1829_, 3, v___x_1827_);
lean_closure_set(v___f_1829_, 4, v___x_1828_);
v___x_1830_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1817_, v_inst_1818_, v_inst_1819_, v_inst_1820_, v_inst_1821_, v_n_1814_);
v___x_1831_ = lean_apply_4(v_toBind_1822_, lean_box(0), lean_box(0), v___x_1830_, v___f_1829_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1835_, lean_object* v_n_1836_, lean_object* v_toPure_1837_, lean_object* v___x_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_toBind_1844_, lean_object* v___y_1845_, lean_object* v_____do__lift_1846_){
_start:
{
uint8_t v___x_427__boxed_1847_; uint8_t v___y_433__boxed_1848_; uint8_t v_____do__lift_434__boxed_1849_; lean_object* v_res_1850_; 
v___x_427__boxed_1847_ = lean_unbox(v___x_1838_);
v___y_433__boxed_1848_ = lean_unbox(v___y_1845_);
v_____do__lift_434__boxed_1849_ = lean_unbox(v_____do__lift_1846_);
v_res_1850_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1835_, v_n_1836_, v_toPure_1837_, v___x_427__boxed_1847_, v_inst_1839_, v_inst_1840_, v_inst_1841_, v_inst_1842_, v_inst_1843_, v_toBind_1844_, v___y_433__boxed_1848_, v_____do__lift_434__boxed_1849_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1851_, lean_object* v_toPure_1852_, uint8_t v___x_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_toBind_1859_, uint8_t v___y_1860_, lean_object* v___x_1861_, lean_object* v_env_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1863_ = lean_box(v___x_1853_);
v___x_1864_ = lean_box(v___y_1860_);
lean_inc(v_toBind_1859_);
lean_inc_ref(v_inst_1856_);
lean_inc_ref(v_inst_1854_);
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1865_, 0, v_env_1862_);
lean_closure_set(v___f_1865_, 1, v_n_1851_);
lean_closure_set(v___f_1865_, 2, v_toPure_1852_);
lean_closure_set(v___f_1865_, 3, v___x_1863_);
lean_closure_set(v___f_1865_, 4, v_inst_1854_);
lean_closure_set(v___f_1865_, 5, v_inst_1855_);
lean_closure_set(v___f_1865_, 6, v_inst_1856_);
lean_closure_set(v___f_1865_, 7, v_inst_1857_);
lean_closure_set(v___f_1865_, 8, v_inst_1858_);
lean_closure_set(v___f_1865_, 9, v_toBind_1859_);
lean_closure_set(v___f_1865_, 10, v___x_1864_);
v___x_1866_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1867_ = l_Lean_Option_getM___redArg(v_inst_1854_, v_inst_1856_, v___x_1861_, v___x_1866_);
v___x_1868_ = lean_apply_4(v_toBind_1859_, lean_box(0), lean_box(0), v___x_1867_, v___f_1865_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1869_, lean_object* v_toPure_1870_, lean_object* v___x_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_toBind_1877_, lean_object* v___y_1878_, lean_object* v___x_1879_, lean_object* v_env_1880_){
_start:
{
uint8_t v___x_469__boxed_1881_; uint8_t v___y_475__boxed_1882_; lean_object* v_res_1883_; 
v___x_469__boxed_1881_ = lean_unbox(v___x_1871_);
v___y_475__boxed_1882_ = lean_unbox(v___y_1878_);
v_res_1883_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1869_, v_toPure_1870_, v___x_469__boxed_1881_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_inst_1875_, v_inst_1876_, v_toBind_1877_, v___y_475__boxed_1882_, v___x_1879_, v_env_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_n_1889_){
_start:
{
lean_object* v___x_1890_; uint8_t v___y_1892_; uint8_t v___x_1907_; 
v___x_1890_ = l_Lean_KVMap_instValueBool;
v___x_1907_ = l_Lean_isPrivateName(v_n_1889_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = 1;
v___y_1892_ = v___x_1908_;
goto v___jp_1891_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = 0;
v___y_1892_ = v___x_1909_;
goto v___jp_1891_;
}
v___jp_1891_:
{
if (v___y_1892_ == 0)
{
lean_object* v_toApplicative_1893_; lean_object* v_toBind_1894_; lean_object* v_toPure_1895_; lean_object* v_getEnv_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; 
v_toApplicative_1893_ = lean_ctor_get(v_inst_1886_, 0);
v_toBind_1894_ = lean_ctor_get(v_inst_1886_, 1);
lean_inc_n(v_toBind_1894_, 2);
v_toPure_1895_ = lean_ctor_get(v_toApplicative_1893_, 1);
lean_inc(v_toPure_1895_);
v_getEnv_1896_ = lean_ctor_get(v_inst_1887_, 0);
lean_inc(v_getEnv_1896_);
v___x_1897_ = 1;
v___x_1898_ = lean_box(v___x_1897_);
v___x_1899_ = lean_box(v___y_1892_);
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1900_, 0, v_n_1889_);
lean_closure_set(v___f_1900_, 1, v_toPure_1895_);
lean_closure_set(v___f_1900_, 2, v___x_1898_);
lean_closure_set(v___f_1900_, 3, v_inst_1886_);
lean_closure_set(v___f_1900_, 4, v_inst_1887_);
lean_closure_set(v___f_1900_, 5, v_inst_1888_);
lean_closure_set(v___f_1900_, 6, v_inst_1884_);
lean_closure_set(v___f_1900_, 7, v_inst_1885_);
lean_closure_set(v___f_1900_, 8, v_toBind_1894_);
lean_closure_set(v___f_1900_, 9, v___x_1899_);
lean_closure_set(v___f_1900_, 10, v___x_1890_);
v___x_1901_ = lean_apply_4(v_toBind_1894_, lean_box(0), lean_box(0), v_getEnv_1896_, v___f_1900_);
return v___x_1901_;
}
else
{
lean_object* v_toApplicative_1902_; lean_object* v_toPure_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_toApplicative_1902_ = lean_ctor_get(v_inst_1886_, 0);
lean_inc_ref(v_toApplicative_1902_);
lean_dec(v_n_1889_);
lean_dec_ref(v_inst_1888_);
lean_dec_ref(v_inst_1887_);
lean_dec_ref(v_inst_1886_);
lean_dec(v_inst_1885_);
lean_dec_ref(v_inst_1884_);
v_toPure_1903_ = lean_ctor_get(v_toApplicative_1902_, 1);
lean_inc(v_toPure_1903_);
lean_dec_ref(v_toApplicative_1902_);
v___x_1904_ = 0;
v___x_1905_ = lean_box(v___x_1904_);
v___x_1906_ = lean_apply_2(v_toPure_1903_, lean_box(0), v___x_1905_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1910_, lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_n_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1911_, v_inst_1912_, v_inst_1913_, v_inst_1914_, v_inst_1915_, v_n_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1918_){
_start:
{
lean_object* v_fst_1919_; uint8_t v___x_1920_; 
v_fst_1919_ = lean_ctor_get(v_x_1918_, 0);
v___x_1920_ = l_Lean_isPrivateName(v_fst_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1921_);
lean_dec_ref(v_x_1921_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1924_, lean_object* v_res_1925_, lean_object* v_____r_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_apply_2(v_toPure_1924_, lean_box(0), v_res_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1928_, lean_object* v_toPure_1929_, lean_object* v_res_1930_, lean_object* v___f_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_toBind_1937_, lean_object* v___f_1938_, lean_object* v_____do__lift_1939_){
_start:
{
if (v_enableLog_1928_ == 0)
{
lean_object* v___x_1940_; 
lean_dec(v___f_1938_);
lean_dec(v_toBind_1937_);
lean_dec(v_inst_1936_);
lean_dec_ref(v_inst_1935_);
lean_dec_ref(v_inst_1934_);
lean_dec_ref(v_inst_1933_);
lean_dec_ref(v_inst_1932_);
lean_dec_ref(v___f_1931_);
v___x_1940_ = lean_apply_2(v_toPure_1929_, lean_box(0), v_res_1930_);
return v___x_1940_;
}
else
{
uint8_t v_isExporting_1941_; 
v_isExporting_1941_ = lean_ctor_get_uint8(v_____do__lift_1939_, sizeof(void*)*13);
if (v_isExporting_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_dec(v___f_1938_);
lean_dec(v_toBind_1937_);
lean_dec(v_inst_1936_);
lean_dec_ref(v_inst_1935_);
lean_dec_ref(v_inst_1934_);
lean_dec_ref(v_inst_1933_);
lean_dec_ref(v_inst_1932_);
lean_dec_ref(v___f_1931_);
v___x_1942_ = lean_apply_2(v_toPure_1929_, lean_box(0), v_res_1930_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; 
lean_inc(v_res_1930_);
v___x_1943_ = l_List_find_x3f___redArg(v___f_1931_, v_res_1930_);
if (lean_obj_tag(v___x_1943_) == 1)
{
lean_object* v_val_1944_; lean_object* v_fst_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v_res_1930_);
lean_dec(v_toPure_1929_);
v_val_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v_fst_1945_ = lean_ctor_get(v_val_1944_, 0);
lean_inc(v_fst_1945_);
lean_dec(v_val_1944_);
v___x_1946_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1932_, v_inst_1933_, v_inst_1934_, v_inst_1935_, v_inst_1936_, v_fst_1945_);
v___x_1947_ = lean_apply_4(v_toBind_1937_, lean_box(0), lean_box(0), v___x_1946_, v___f_1938_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; 
lean_dec(v___x_1943_);
lean_dec(v___f_1938_);
lean_dec(v_toBind_1937_);
lean_dec(v_inst_1936_);
lean_dec_ref(v_inst_1935_);
lean_dec_ref(v_inst_1934_);
lean_dec_ref(v_inst_1933_);
lean_dec_ref(v_inst_1932_);
v___x_1948_ = lean_apply_2(v_toPure_1929_, lean_box(0), v_res_1930_);
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1949_, lean_object* v_toPure_1950_, lean_object* v_res_1951_, lean_object* v___f_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_toBind_1958_, lean_object* v___f_1959_, lean_object* v_____do__lift_1960_){
_start:
{
uint8_t v_enableLog_boxed_1961_; lean_object* v_res_1962_; 
v_enableLog_boxed_1961_ = lean_unbox(v_enableLog_1949_);
v_res_1962_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1961_, v_toPure_1950_, v_res_1951_, v___f_1952_, v_inst_1953_, v_inst_1954_, v_inst_1955_, v_inst_1956_, v_inst_1957_, v_toBind_1958_, v___f_1959_, v_____do__lift_1960_);
lean_dec_ref(v_____do__lift_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1963_, lean_object* v_____do__lift_1964_, lean_object* v_____do__lift_1965_, lean_object* v_id_1966_, lean_object* v_toPure_1967_, uint8_t v_enableLog_1968_, lean_object* v___f_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_toBind_1975_, lean_object* v_getEnv_1976_, lean_object* v_____do__lift_1977_){
_start:
{
lean_object* v_res_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; 
v_res_1978_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1963_, v_____do__lift_1964_, v_____do__lift_1965_, v_____do__lift_1977_, v_id_1966_);
lean_inc(v_res_1978_);
lean_inc(v_toPure_1967_);
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1979_, 0, v_toPure_1967_);
lean_closure_set(v___f_1979_, 1, v_res_1978_);
v___x_1980_ = lean_box(v_enableLog_1968_);
lean_inc(v_toBind_1975_);
v___f_1981_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1981_, 0, v___x_1980_);
lean_closure_set(v___f_1981_, 1, v_toPure_1967_);
lean_closure_set(v___f_1981_, 2, v_res_1978_);
lean_closure_set(v___f_1981_, 3, v___f_1969_);
lean_closure_set(v___f_1981_, 4, v_inst_1970_);
lean_closure_set(v___f_1981_, 5, v_inst_1971_);
lean_closure_set(v___f_1981_, 6, v_inst_1972_);
lean_closure_set(v___f_1981_, 7, v_inst_1973_);
lean_closure_set(v___f_1981_, 8, v_inst_1974_);
lean_closure_set(v___f_1981_, 9, v_toBind_1975_);
lean_closure_set(v___f_1981_, 10, v___f_1979_);
v___x_1982_ = lean_apply_4(v_toBind_1975_, lean_box(0), lean_box(0), v_getEnv_1976_, v___f_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1983_, lean_object* v_____do__lift_1984_, lean_object* v_____do__lift_1985_, lean_object* v_id_1986_, lean_object* v_toPure_1987_, lean_object* v_enableLog_1988_, lean_object* v___f_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_toBind_1995_, lean_object* v_getEnv_1996_, lean_object* v_____do__lift_1997_){
_start:
{
uint8_t v_enableLog_boxed_1998_; lean_object* v_res_1999_; 
v_enableLog_boxed_1998_ = lean_unbox(v_enableLog_1988_);
v_res_1999_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1983_, v_____do__lift_1984_, v_____do__lift_1985_, v_id_1986_, v_toPure_1987_, v_enableLog_boxed_1998_, v___f_1989_, v_inst_1990_, v_inst_1991_, v_inst_1992_, v_inst_1993_, v_inst_1994_, v_toBind_1995_, v_getEnv_1996_, v_____do__lift_1997_);
lean_dec_ref(v_____do__lift_1984_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_2000_, lean_object* v_____do__lift_2001_, lean_object* v_id_2002_, lean_object* v_toPure_2003_, uint8_t v_enableLog_2004_, lean_object* v___f_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_toBind_2011_, lean_object* v_getEnv_2012_, lean_object* v_getOpenDecls_2013_, lean_object* v_____do__lift_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; 
v___x_2015_ = lean_box(v_enableLog_2004_);
lean_inc(v_toBind_2011_);
v___f_2016_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_2016_, 0, v_____do__lift_2000_);
lean_closure_set(v___f_2016_, 1, v_____do__lift_2001_);
lean_closure_set(v___f_2016_, 2, v_____do__lift_2014_);
lean_closure_set(v___f_2016_, 3, v_id_2002_);
lean_closure_set(v___f_2016_, 4, v_toPure_2003_);
lean_closure_set(v___f_2016_, 5, v___x_2015_);
lean_closure_set(v___f_2016_, 6, v___f_2005_);
lean_closure_set(v___f_2016_, 7, v_inst_2006_);
lean_closure_set(v___f_2016_, 8, v_inst_2007_);
lean_closure_set(v___f_2016_, 9, v_inst_2008_);
lean_closure_set(v___f_2016_, 10, v_inst_2009_);
lean_closure_set(v___f_2016_, 11, v_inst_2010_);
lean_closure_set(v___f_2016_, 12, v_toBind_2011_);
lean_closure_set(v___f_2016_, 13, v_getEnv_2012_);
v___x_2017_ = lean_apply_4(v_toBind_2011_, lean_box(0), lean_box(0), v_getOpenDecls_2013_, v___f_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_2018_, lean_object* v_____do__lift_2019_, lean_object* v_id_2020_, lean_object* v_toPure_2021_, lean_object* v_enableLog_2022_, lean_object* v___f_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_toBind_2029_, lean_object* v_getEnv_2030_, lean_object* v_getOpenDecls_2031_, lean_object* v_____do__lift_2032_){
_start:
{
uint8_t v_enableLog_boxed_2033_; lean_object* v_res_2034_; 
v_enableLog_boxed_2033_ = lean_unbox(v_enableLog_2022_);
v_res_2034_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_2018_, v_____do__lift_2019_, v_id_2020_, v_toPure_2021_, v_enableLog_boxed_2033_, v___f_2023_, v_inst_2024_, v_inst_2025_, v_inst_2026_, v_inst_2027_, v_inst_2028_, v_toBind_2029_, v_getEnv_2030_, v_getOpenDecls_2031_, v_____do__lift_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_2035_, lean_object* v_____do__lift_2036_, lean_object* v_id_2037_, lean_object* v_toPure_2038_, uint8_t v_enableLog_2039_, lean_object* v___f_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_toBind_2046_, lean_object* v_getEnv_2047_, lean_object* v_____do__lift_2048_){
_start:
{
lean_object* v_getCurrNamespace_2049_; lean_object* v_getOpenDecls_2050_; lean_object* v___x_2051_; lean_object* v___f_2052_; lean_object* v___x_2053_; 
v_getCurrNamespace_2049_ = lean_ctor_get(v_inst_2035_, 0);
lean_inc(v_getCurrNamespace_2049_);
v_getOpenDecls_2050_ = lean_ctor_get(v_inst_2035_, 1);
lean_inc(v_getOpenDecls_2050_);
lean_dec_ref(v_inst_2035_);
v___x_2051_ = lean_box(v_enableLog_2039_);
lean_inc(v_toBind_2046_);
v___f_2052_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_2052_, 0, v_____do__lift_2036_);
lean_closure_set(v___f_2052_, 1, v_____do__lift_2048_);
lean_closure_set(v___f_2052_, 2, v_id_2037_);
lean_closure_set(v___f_2052_, 3, v_toPure_2038_);
lean_closure_set(v___f_2052_, 4, v___x_2051_);
lean_closure_set(v___f_2052_, 5, v___f_2040_);
lean_closure_set(v___f_2052_, 6, v_inst_2041_);
lean_closure_set(v___f_2052_, 7, v_inst_2042_);
lean_closure_set(v___f_2052_, 8, v_inst_2043_);
lean_closure_set(v___f_2052_, 9, v_inst_2044_);
lean_closure_set(v___f_2052_, 10, v_inst_2045_);
lean_closure_set(v___f_2052_, 11, v_toBind_2046_);
lean_closure_set(v___f_2052_, 12, v_getEnv_2047_);
lean_closure_set(v___f_2052_, 13, v_getOpenDecls_2050_);
v___x_2053_ = lean_apply_4(v_toBind_2046_, lean_box(0), lean_box(0), v_getCurrNamespace_2049_, v___f_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_2054_, lean_object* v_____do__lift_2055_, lean_object* v_id_2056_, lean_object* v_toPure_2057_, lean_object* v_enableLog_2058_, lean_object* v___f_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_toBind_2065_, lean_object* v_getEnv_2066_, lean_object* v_____do__lift_2067_){
_start:
{
uint8_t v_enableLog_boxed_2068_; lean_object* v_res_2069_; 
v_enableLog_boxed_2068_ = lean_unbox(v_enableLog_2058_);
v_res_2069_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_2054_, v_____do__lift_2055_, v_id_2056_, v_toPure_2057_, v_enableLog_boxed_2068_, v___f_2059_, v_inst_2060_, v_inst_2061_, v_inst_2062_, v_inst_2063_, v_inst_2064_, v_toBind_2065_, v_getEnv_2066_, v_____do__lift_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_id_2072_, lean_object* v_toPure_2073_, uint8_t v_enableLog_2074_, lean_object* v___f_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_toBind_2080_, lean_object* v_getEnv_2081_, lean_object* v_____do__lift_2082_){
_start:
{
lean_object* v_getOptions_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; 
v_getOptions_2083_ = lean_ctor_get(v_inst_2070_, 0);
lean_inc(v_getOptions_2083_);
v___x_2084_ = lean_box(v_enableLog_2074_);
lean_inc(v_toBind_2080_);
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_2085_, 0, v_inst_2071_);
lean_closure_set(v___f_2085_, 1, v_____do__lift_2082_);
lean_closure_set(v___f_2085_, 2, v_id_2072_);
lean_closure_set(v___f_2085_, 3, v_toPure_2073_);
lean_closure_set(v___f_2085_, 4, v___x_2084_);
lean_closure_set(v___f_2085_, 5, v___f_2075_);
lean_closure_set(v___f_2085_, 6, v_inst_2076_);
lean_closure_set(v___f_2085_, 7, v_inst_2077_);
lean_closure_set(v___f_2085_, 8, v_inst_2070_);
lean_closure_set(v___f_2085_, 9, v_inst_2078_);
lean_closure_set(v___f_2085_, 10, v_inst_2079_);
lean_closure_set(v___f_2085_, 11, v_toBind_2080_);
lean_closure_set(v___f_2085_, 12, v_getEnv_2081_);
v___x_2086_ = lean_apply_4(v_toBind_2080_, lean_box(0), lean_box(0), v_getOptions_2083_, v___f_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_id_2089_, lean_object* v_toPure_2090_, lean_object* v_enableLog_2091_, lean_object* v___f_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_toBind_2097_, lean_object* v_getEnv_2098_, lean_object* v_____do__lift_2099_){
_start:
{
uint8_t v_enableLog_boxed_2100_; lean_object* v_res_2101_; 
v_enableLog_boxed_2100_ = lean_unbox(v_enableLog_2091_);
v_res_2101_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2087_, v_inst_2088_, v_id_2089_, v_toPure_2090_, v_enableLog_boxed_2100_, v___f_2092_, v_inst_2093_, v_inst_2094_, v_inst_2095_, v_inst_2096_, v_toBind_2097_, v_getEnv_2098_, v_____do__lift_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_id_2109_, uint8_t v_enableLog_2110_){
_start:
{
lean_object* v_toApplicative_2111_; lean_object* v_toBind_2112_; lean_object* v_getEnv_2113_; lean_object* v_toPure_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; 
v_toApplicative_2111_ = lean_ctor_get(v_inst_2103_, 0);
v_toBind_2112_ = lean_ctor_get(v_inst_2103_, 1);
lean_inc_n(v_toBind_2112_, 2);
v_getEnv_2113_ = lean_ctor_get(v_inst_2105_, 0);
lean_inc_n(v_getEnv_2113_, 2);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2111_, 1);
lean_inc(v_toPure_2114_);
v___f_2115_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2116_ = lean_box(v_enableLog_2110_);
v___f_2117_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2117_, 0, v_inst_2106_);
lean_closure_set(v___f_2117_, 1, v_inst_2104_);
lean_closure_set(v___f_2117_, 2, v_id_2109_);
lean_closure_set(v___f_2117_, 3, v_toPure_2114_);
lean_closure_set(v___f_2117_, 4, v___x_2116_);
lean_closure_set(v___f_2117_, 5, v___f_2115_);
lean_closure_set(v___f_2117_, 6, v_inst_2103_);
lean_closure_set(v___f_2117_, 7, v_inst_2105_);
lean_closure_set(v___f_2117_, 8, v_inst_2107_);
lean_closure_set(v___f_2117_, 9, v_inst_2108_);
lean_closure_set(v___f_2117_, 10, v_toBind_2112_);
lean_closure_set(v___f_2117_, 11, v_getEnv_2113_);
v___x_2118_ = lean_apply_4(v_toBind_2112_, lean_box(0), lean_box(0), v_getEnv_2113_, v___f_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_id_2125_, lean_object* v_enableLog_2126_){
_start:
{
uint8_t v_enableLog_boxed_2127_; lean_object* v_res_2128_; 
v_enableLog_boxed_2127_ = lean_unbox(v_enableLog_2126_);
v_res_2128_ = l_Lean_resolveGlobalName___redArg(v_inst_2119_, v_inst_2120_, v_inst_2121_, v_inst_2122_, v_inst_2123_, v_inst_2124_, v_id_2125_, v_enableLog_boxed_2127_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_id_2136_, uint8_t v_enableLog_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_resolveGlobalName___redArg(v_inst_2130_, v_inst_2131_, v_inst_2132_, v_inst_2133_, v_inst_2134_, v_inst_2135_, v_id_2136_, v_enableLog_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_id_2146_, lean_object* v_enableLog_2147_){
_start:
{
uint8_t v_enableLog_boxed_2148_; lean_object* v_res_2149_; 
v_enableLog_boxed_2148_ = lean_unbox(v_enableLog_2147_);
v_res_2149_ = l_Lean_resolveGlobalName(v_m_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_, v_inst_2144_, v_inst_2145_, v_id_2146_, v_enableLog_boxed_2148_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2150_, lean_object* v_nss_2151_, lean_object* v_____r_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_apply_2(v_toPure_2150_, lean_box(0), v_nss_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2156_, lean_object* v_____do__lift_2157_, lean_object* v_id_2158_, uint8_t v_allowEmpty_2159_, lean_object* v_toPure_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_toBind_2163_, lean_object* v_____do__lift_2164_){
_start:
{
lean_object* v_nss_2165_; 
lean_inc(v_id_2158_);
v_nss_2165_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2156_, v_____do__lift_2157_, v_____do__lift_2164_, v_id_2158_);
if (v_allowEmpty_2159_ == 0)
{
uint8_t v___x_2166_; 
v___x_2166_ = l_List_isEmpty___redArg(v_nss_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
lean_dec(v_toBind_2163_);
lean_dec_ref(v_inst_2162_);
lean_dec_ref(v_inst_2161_);
lean_dec(v_id_2158_);
v___x_2167_ = lean_apply_2(v_toPure_2160_, lean_box(0), v_nss_2165_);
return v___x_2167_;
}
else
{
lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___f_2168_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2168_, 0, v_toPure_2160_);
lean_closure_set(v___f_2168_, 1, v_nss_2165_);
v___x_2169_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2170_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2158_, v___x_2166_);
v___x_2171_ = lean_string_append(v___x_2169_, v___x_2170_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2173_ = lean_string_append(v___x_2171_, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
v___x_2175_ = l_Lean_MessageData_ofFormat(v___x_2174_);
v___x_2176_ = l_Lean_throwError___redArg(v_inst_2161_, v_inst_2162_, v___x_2175_);
v___x_2177_ = lean_apply_4(v_toBind_2163_, lean_box(0), lean_box(0), v___x_2176_, v___f_2168_);
return v___x_2177_;
}
}
else
{
lean_object* v___x_2178_; 
lean_dec(v_toBind_2163_);
lean_dec_ref(v_inst_2162_);
lean_dec_ref(v_inst_2161_);
lean_dec(v_id_2158_);
v___x_2178_ = lean_apply_2(v_toPure_2160_, lean_box(0), v_nss_2165_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2179_, lean_object* v_____do__lift_2180_, lean_object* v_id_2181_, lean_object* v_allowEmpty_2182_, lean_object* v_toPure_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_toBind_2186_, lean_object* v_____do__lift_2187_){
_start:
{
uint8_t v_allowEmpty_boxed_2188_; lean_object* v_res_2189_; 
v_allowEmpty_boxed_2188_ = lean_unbox(v_allowEmpty_2182_);
v_res_2189_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2179_, v_____do__lift_2180_, v_id_2181_, v_allowEmpty_boxed_2188_, v_toPure_2183_, v_inst_2184_, v_inst_2185_, v_toBind_2186_, v_____do__lift_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2190_, lean_object* v_id_2191_, uint8_t v_allowEmpty_2192_, lean_object* v_toPure_2193_, lean_object* v_inst_2194_, lean_object* v_inst_2195_, lean_object* v_toBind_2196_, lean_object* v_getOpenDecls_2197_, lean_object* v_____do__lift_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___f_2200_; lean_object* v___x_2201_; 
v___x_2199_ = lean_box(v_allowEmpty_2192_);
lean_inc(v_toBind_2196_);
v___f_2200_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2200_, 0, v_____do__lift_2190_);
lean_closure_set(v___f_2200_, 1, v_____do__lift_2198_);
lean_closure_set(v___f_2200_, 2, v_id_2191_);
lean_closure_set(v___f_2200_, 3, v___x_2199_);
lean_closure_set(v___f_2200_, 4, v_toPure_2193_);
lean_closure_set(v___f_2200_, 5, v_inst_2194_);
lean_closure_set(v___f_2200_, 6, v_inst_2195_);
lean_closure_set(v___f_2200_, 7, v_toBind_2196_);
v___x_2201_ = lean_apply_4(v_toBind_2196_, lean_box(0), lean_box(0), v_getOpenDecls_2197_, v___f_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2202_, lean_object* v_id_2203_, lean_object* v_allowEmpty_2204_, lean_object* v_toPure_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_toBind_2208_, lean_object* v_getOpenDecls_2209_, lean_object* v_____do__lift_2210_){
_start:
{
uint8_t v_allowEmpty_boxed_2211_; lean_object* v_res_2212_; 
v_allowEmpty_boxed_2211_ = lean_unbox(v_allowEmpty_2204_);
v_res_2212_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2202_, v_id_2203_, v_allowEmpty_boxed_2211_, v_toPure_2205_, v_inst_2206_, v_inst_2207_, v_toBind_2208_, v_getOpenDecls_2209_, v_____do__lift_2210_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2213_, lean_object* v_id_2214_, uint8_t v_allowEmpty_2215_, lean_object* v_toPure_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_toBind_2219_, lean_object* v_____do__lift_2220_){
_start:
{
lean_object* v_getCurrNamespace_2221_; lean_object* v_getOpenDecls_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; 
v_getCurrNamespace_2221_ = lean_ctor_get(v_inst_2213_, 0);
lean_inc(v_getCurrNamespace_2221_);
v_getOpenDecls_2222_ = lean_ctor_get(v_inst_2213_, 1);
lean_inc(v_getOpenDecls_2222_);
lean_dec_ref(v_inst_2213_);
v___x_2223_ = lean_box(v_allowEmpty_2215_);
lean_inc(v_toBind_2219_);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2224_, 0, v_____do__lift_2220_);
lean_closure_set(v___f_2224_, 1, v_id_2214_);
lean_closure_set(v___f_2224_, 2, v___x_2223_);
lean_closure_set(v___f_2224_, 3, v_toPure_2216_);
lean_closure_set(v___f_2224_, 4, v_inst_2217_);
lean_closure_set(v___f_2224_, 5, v_inst_2218_);
lean_closure_set(v___f_2224_, 6, v_toBind_2219_);
lean_closure_set(v___f_2224_, 7, v_getOpenDecls_2222_);
v___x_2225_ = lean_apply_4(v_toBind_2219_, lean_box(0), lean_box(0), v_getCurrNamespace_2221_, v___f_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2226_, lean_object* v_id_2227_, lean_object* v_allowEmpty_2228_, lean_object* v_toPure_2229_, lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_toBind_2232_, lean_object* v_____do__lift_2233_){
_start:
{
uint8_t v_allowEmpty_boxed_2234_; lean_object* v_res_2235_; 
v_allowEmpty_boxed_2234_ = lean_unbox(v_allowEmpty_2228_);
v_res_2235_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2226_, v_id_2227_, v_allowEmpty_boxed_2234_, v_toPure_2229_, v_inst_2230_, v_inst_2231_, v_toBind_2232_, v_____do__lift_2233_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_id_2240_, uint8_t v_allowEmpty_2241_){
_start:
{
lean_object* v_toApplicative_2242_; lean_object* v_toBind_2243_; lean_object* v_getEnv_2244_; lean_object* v_toPure_2245_; lean_object* v___x_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; 
v_toApplicative_2242_ = lean_ctor_get(v_inst_2236_, 0);
v_toBind_2243_ = lean_ctor_get(v_inst_2236_, 1);
lean_inc_n(v_toBind_2243_, 2);
v_getEnv_2244_ = lean_ctor_get(v_inst_2238_, 0);
lean_inc(v_getEnv_2244_);
lean_dec_ref(v_inst_2238_);
v_toPure_2245_ = lean_ctor_get(v_toApplicative_2242_, 1);
lean_inc(v_toPure_2245_);
v___x_2246_ = lean_box(v_allowEmpty_2241_);
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2247_, 0, v_inst_2237_);
lean_closure_set(v___f_2247_, 1, v_id_2240_);
lean_closure_set(v___f_2247_, 2, v___x_2246_);
lean_closure_set(v___f_2247_, 3, v_toPure_2245_);
lean_closure_set(v___f_2247_, 4, v_inst_2236_);
lean_closure_set(v___f_2247_, 5, v_inst_2239_);
lean_closure_set(v___f_2247_, 6, v_toBind_2243_);
v___x_2248_ = lean_apply_4(v_toBind_2243_, lean_box(0), lean_box(0), v_getEnv_2244_, v___f_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_id_2253_, lean_object* v_allowEmpty_2254_){
_start:
{
uint8_t v_allowEmpty_boxed_2255_; lean_object* v_res_2256_; 
v_allowEmpty_boxed_2255_ = lean_unbox(v_allowEmpty_2254_);
v_res_2256_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2249_, v_inst_2250_, v_inst_2251_, v_inst_2252_, v_id_2253_, v_allowEmpty_boxed_2255_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_id_2262_, uint8_t v_allowEmpty_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2258_, v_inst_2259_, v_inst_2260_, v_inst_2261_, v_id_2262_, v_allowEmpty_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_id_2270_, lean_object* v_allowEmpty_2271_){
_start:
{
uint8_t v_allowEmpty_boxed_2272_; lean_object* v_res_2273_; 
v_allowEmpty_boxed_2272_ = lean_unbox(v_allowEmpty_2271_);
v_res_2273_ = l_Lean_resolveNamespaceCore(v_m_2265_, v_inst_2266_, v_inst_2267_, v_inst_2268_, v_inst_2269_, v_id_2270_, v_allowEmpty_boxed_2272_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2274_){
_start:
{
if (lean_obj_tag(v_x_2274_) == 0)
{
lean_object* v_ns_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_ns_2275_ = lean_ctor_get(v_x_2274_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_x_2274_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v_x_2274_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_ns_2275_);
lean_dec(v_x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set_tag(v___x_2277_, 1);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_ns_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_object* v___x_2283_; 
lean_dec_ref(v_x_2274_);
v___x_2283_ = lean_box(0);
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2284_, lean_object* v_withRef_2285_, lean_object* v___x_2286_, lean_object* v_oldRef_2287_){
_start:
{
lean_object* v_ref_2288_; lean_object* v___x_2289_; 
v_ref_2288_ = l_Lean_replaceRef(v_x_2284_, v_oldRef_2287_);
v___x_2289_ = lean_apply_3(v_withRef_2285_, lean_box(0), v_ref_2288_, v___x_2286_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2290_, lean_object* v_withRef_2291_, lean_object* v___x_2292_, lean_object* v_oldRef_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2290_, v_withRef_2291_, v___x_2292_, v_oldRef_2293_);
lean_dec(v_oldRef_2293_);
lean_dec(v_x_2290_);
return v_res_2294_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2302_ = l_Lean_MessageData_ofFormat(v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_x_2307_){
_start:
{
if (lean_obj_tag(v_x_2307_) == 3)
{
lean_object* v_toApplicative_2308_; lean_object* v_toBind_2309_; lean_object* v_toPure_2310_; lean_object* v_toMonadRef_2311_; lean_object* v_val_2312_; lean_object* v_preresolved_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; lean_object* v_pre_2316_; uint8_t v___x_2317_; 
v_toApplicative_2308_ = lean_ctor_get(v_inst_2303_, 0);
v_toBind_2309_ = lean_ctor_get(v_inst_2303_, 1);
lean_inc(v_toBind_2309_);
v_toPure_2310_ = lean_ctor_get(v_toApplicative_2308_, 1);
v_toMonadRef_2311_ = lean_ctor_get(v_inst_2306_, 1);
v_val_2312_ = lean_ctor_get(v_x_2307_, 2);
v_preresolved_2313_ = lean_ctor_get(v_x_2307_, 3);
v___f_2314_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2315_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2313_);
v_pre_2316_ = l_List_filterMapTR_go___redArg(v___f_2314_, v_preresolved_2313_, v___x_2315_);
v___x_2317_ = l_List_isEmpty___redArg(v_pre_2316_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
lean_inc(v_toPure_2310_);
lean_dec_ref_known(v_x_2307_, 4);
lean_dec(v_toBind_2309_);
lean_dec_ref(v_inst_2306_);
lean_dec_ref(v_inst_2305_);
lean_dec_ref(v_inst_2304_);
lean_dec_ref(v_inst_2303_);
v___x_2318_ = lean_apply_2(v_toPure_2310_, lean_box(0), v_pre_2316_);
return v___x_2318_;
}
else
{
lean_object* v_getRef_2319_; lean_object* v_withRef_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; 
lean_dec(v_pre_2316_);
v_getRef_2319_ = lean_ctor_get(v_toMonadRef_2311_, 0);
lean_inc(v_getRef_2319_);
v_withRef_2320_ = lean_ctor_get(v_toMonadRef_2311_, 1);
lean_inc(v_withRef_2320_);
v___x_2321_ = 0;
lean_inc(v_val_2312_);
v___x_2322_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2303_, v_inst_2304_, v_inst_2305_, v_inst_2306_, v_val_2312_, v___x_2321_);
v___f_2323_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2323_, 0, v_x_2307_);
lean_closure_set(v___f_2323_, 1, v_withRef_2320_);
lean_closure_set(v___f_2323_, 2, v___x_2322_);
v___x_2324_ = lean_apply_4(v_toBind_2309_, lean_box(0), lean_box(0), v_getRef_2319_, v___f_2323_);
return v___x_2324_;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v_inst_2305_);
lean_dec_ref(v_inst_2304_);
v___x_2325_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2326_ = l_Lean_throwErrorAt___redArg(v_inst_2303_, v_inst_2306_, v_x_2307_, v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_x_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_resolveNamespace___redArg(v_inst_2328_, v_inst_2329_, v_inst_2330_, v_inst_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2336_, lean_object* v___f_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_toPure_2340_, lean_object* v_____do__lift_2341_){
_start:
{
if (lean_obj_tag(v_____do__lift_2341_) == 1)
{
lean_object* v_tail_2357_; 
v_tail_2357_ = lean_ctor_get(v_____do__lift_2341_, 1);
if (lean_obj_tag(v_tail_2357_) == 0)
{
lean_object* v_head_2358_; lean_object* v___x_2359_; 
lean_dec_ref(v_inst_2339_);
lean_dec_ref(v_inst_2338_);
lean_dec_ref(v___f_2337_);
v_head_2358_ = lean_ctor_get(v_____do__lift_2341_, 0);
lean_inc(v_head_2358_);
lean_dec_ref_known(v_____do__lift_2341_, 2);
v___x_2359_ = lean_apply_2(v_toPure_2340_, lean_box(0), v_head_2358_);
return v___x_2359_;
}
else
{
lean_dec(v_toPure_2340_);
goto v___jp_2342_;
}
}
else
{
lean_dec(v_toPure_2340_);
goto v___jp_2342_;
}
v___jp_2342_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2343_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2344_ = l_Lean_TSyntax_getId(v_id_2336_);
v___x_2345_ = 1;
v___x_2346_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2344_, v___x_2345_);
v___x_2347_ = lean_string_append(v___x_2343_, v___x_2346_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
v___x_2350_ = l_List_toString___redArg(v___f_2337_, v_____do__lift_2341_);
v___x_2351_ = lean_string_append(v___x_2349_, v___x_2350_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2353_ = lean_string_append(v___x_2351_, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
v___x_2355_ = l_Lean_MessageData_ofFormat(v___x_2354_);
v___x_2356_ = l_Lean_throwError___redArg(v_inst_2338_, v_inst_2339_, v___x_2355_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2360_, lean_object* v___f_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_toPure_2364_, lean_object* v_____do__lift_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2360_, v___f_2361_, v_inst_2362_, v_inst_2363_, v_toPure_2364_, v_____do__lift_2365_);
lean_dec(v_id_2360_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_id_2372_){
_start:
{
lean_object* v_toApplicative_2373_; lean_object* v_toBind_2374_; lean_object* v_toPure_2375_; lean_object* v___f_2376_; lean_object* v___x_2377_; lean_object* v___f_2378_; lean_object* v___x_2379_; 
v_toApplicative_2373_ = lean_ctor_get(v_inst_2368_, 0);
v_toBind_2374_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2374_);
v_toPure_2375_ = lean_ctor_get(v_toApplicative_2373_, 1);
lean_inc(v_toPure_2375_);
v___f_2376_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2372_);
lean_inc_ref(v_inst_2371_);
lean_inc_ref(v_inst_2368_);
v___x_2377_ = l_Lean_resolveNamespace___redArg(v_inst_2368_, v_inst_2369_, v_inst_2370_, v_inst_2371_, v_id_2372_);
v___f_2378_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2378_, 0, v_id_2372_);
lean_closure_set(v___f_2378_, 1, v___f_2376_);
lean_closure_set(v___f_2378_, 2, v_inst_2368_);
lean_closure_set(v___f_2378_, 3, v_inst_2371_);
lean_closure_set(v___f_2378_, 4, v_toPure_2375_);
v___x_2379_ = lean_apply_4(v_toBind_2374_, lean_box(0), lean_box(0), v___x_2377_, v___f_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_id_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2381_, v_inst_2382_, v_inst_2383_, v_inst_2384_, v_id_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2387_){
_start:
{
lean_object* v_snd_2388_; uint8_t v___x_2389_; 
v_snd_2388_ = lean_ctor_get(v_x_2387_, 1);
v___x_2389_ = l_List_isEmpty___redArg(v_snd_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2390_){
_start:
{
uint8_t v_res_2391_; lean_object* v_r_2392_; 
v_res_2391_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2390_);
lean_dec_ref(v_x_2390_);
v_r_2392_ = lean_box(v_res_2391_);
return v_r_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2393_){
_start:
{
lean_object* v_fst_2394_; 
v_fst_2394_ = lean_ctor_get(v_x_2393_, 0);
lean_inc(v_fst_2394_);
return v_fst_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2395_);
lean_dec_ref(v_x_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2397_, lean_object* v_cs_2398_, lean_object* v_toPure_2399_, lean_object* v_____r_2400_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_List_mapTR_loop___redArg(v___f_2397_, v_cs_2398_, v___x_2401_);
v___x_2403_ = lean_apply_2(v_toPure_2399_, lean_box(0), v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2404_, lean_object* v_____r_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_apply_1(v___f_2404_, v_____r_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_n_2410_, lean_object* v_toBind_2411_, lean_object* v___f_2412_, lean_object* v_____do__lift_2413_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2407_, v_inst_2408_, v_inst_2409_, v_____do__lift_2413_, v_n_2410_);
v___x_2415_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___x_2414_, v___f_2412_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_n_2421_, lean_object* v_cs_2422_){
_start:
{
lean_object* v_toApplicative_2423_; lean_object* v_toBind_2424_; lean_object* v_toPure_2425_; lean_object* v_toMonadRef_2426_; lean_object* v___f_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v_cs_2430_; lean_object* v___f_2431_; uint8_t v___x_2432_; 
v_toApplicative_2423_ = lean_ctor_get(v_inst_2418_, 0);
v_toBind_2424_ = lean_ctor_get(v_inst_2418_, 1);
lean_inc(v_toBind_2424_);
v_toPure_2425_ = lean_ctor_get(v_toApplicative_2423_, 1);
v_toMonadRef_2426_ = lean_ctor_get(v_inst_2420_, 1);
v___f_2427_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2428_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2429_ = lean_box(0);
v_cs_2430_ = l_List_filterTR_loop___redArg(v___f_2427_, v_cs_2422_, v___x_2429_);
lean_inc(v_toPure_2425_);
lean_inc(v_cs_2430_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2431_, 0, v___f_2428_);
lean_closure_set(v___f_2431_, 1, v_cs_2430_);
lean_closure_set(v___f_2431_, 2, v_toPure_2425_);
v___x_2432_ = l_List_isEmpty___redArg(v_cs_2430_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_inc(v_toPure_2425_);
lean_dec_ref(v___f_2431_);
lean_dec(v_toBind_2424_);
lean_dec(v_n_2421_);
lean_dec_ref(v_inst_2420_);
lean_dec_ref(v_inst_2419_);
lean_dec_ref(v_inst_2418_);
v___x_2433_ = lean_box(0);
v___x_2434_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2428_, v_cs_2430_, v_toPure_2425_, v___x_2433_);
return v___x_2434_;
}
else
{
lean_object* v_getRef_2435_; lean_object* v___f_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; 
lean_dec(v_cs_2430_);
v_getRef_2435_ = lean_ctor_get(v_toMonadRef_2426_, 0);
lean_inc(v_getRef_2435_);
v___f_2436_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2436_, 0, v___f_2431_);
lean_inc(v_toBind_2424_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2437_, 0, v_inst_2418_);
lean_closure_set(v___f_2437_, 1, v_inst_2419_);
lean_closure_set(v___f_2437_, 2, v_inst_2420_);
lean_closure_set(v___f_2437_, 3, v_n_2421_);
lean_closure_set(v___f_2437_, 4, v_toBind_2424_);
lean_closure_set(v___f_2437_, 5, v___f_2436_);
v___x_2438_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v_getRef_2435_, v___f_2437_);
return v___x_2438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_n_2443_, lean_object* v_cs_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_filterFieldList___redArg(v_inst_2440_, v_inst_2441_, v_inst_2442_, v_n_2443_, v_cs_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_n_2449_, lean_object* v_cs_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_filterFieldList___redArg(v_inst_2446_, v_inst_2447_, v_inst_2448_, v_n_2449_, v_cs_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_n_2459_){
_start:
{
lean_object* v_toBind_2460_; lean_object* v___f_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_toBind_2460_ = lean_ctor_get(v_inst_2452_, 1);
lean_inc(v_toBind_2460_);
lean_inc(v_n_2459_);
lean_inc_ref(v_inst_2454_);
lean_inc_ref(v_inst_2452_);
v___f_2461_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2461_, 0, v_inst_2452_);
lean_closure_set(v___f_2461_, 1, v_inst_2454_);
lean_closure_set(v___f_2461_, 2, v_inst_2458_);
lean_closure_set(v___f_2461_, 3, v_n_2459_);
v___x_2462_ = 1;
v___x_2463_ = l_Lean_resolveGlobalName___redArg(v_inst_2452_, v_inst_2453_, v_inst_2454_, v_inst_2455_, v_inst_2456_, v_inst_2457_, v_n_2459_, v___x_2462_);
v___x_2464_ = lean_apply_4(v_toBind_2460_, lean_box(0), lean_box(0), v___x_2463_, v___f_2461_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_n_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2466_, v_inst_2467_, v_inst_2468_, v_inst_2469_, v_inst_2470_, v_inst_2471_, v_inst_2472_, v_n_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2475_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = l_Lean_mkConst(v_declName_2475_, v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2481_ = l_Lean_stringToMessageData(v___x_2480_);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2484_ = l_Lean_stringToMessageData(v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_n_2488_, lean_object* v_cs_2489_){
_start:
{
lean_object* v_toApplicative_2490_; lean_object* v_toPure_2491_; lean_object* v___f_2492_; 
v_toApplicative_2490_ = lean_ctor_get(v_inst_2486_, 0);
v_toPure_2491_ = lean_ctor_get(v_toApplicative_2490_, 1);
v___f_2492_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2489_) == 1)
{
lean_object* v_tail_2506_; 
v_tail_2506_ = lean_ctor_get(v_cs_2489_, 1);
if (lean_obj_tag(v_tail_2506_) == 0)
{
lean_object* v_head_2507_; lean_object* v___x_2508_; 
lean_inc(v_toPure_2491_);
lean_dec(v_n_2488_);
lean_dec_ref(v_inst_2487_);
lean_dec_ref(v_inst_2486_);
v_head_2507_ = lean_ctor_get(v_cs_2489_, 0);
lean_inc(v_head_2507_);
lean_dec_ref_known(v_cs_2489_, 2);
v___x_2508_ = lean_apply_2(v_toPure_2491_, lean_box(0), v_head_2507_);
return v___x_2508_;
}
else
{
goto v___jp_2493_;
}
}
else
{
goto v___jp_2493_;
}
v___jp_2493_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2494_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2495_ = l_Lean_MessageData_ofName(v_n_2488_);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_box(0);
v___x_2500_ = l_List_mapTR_loop___redArg(v___f_2492_, v_cs_2489_, v___x_2499_);
v___x_2501_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2502_ = l_List_mapTR_loop___redArg(v___x_2501_, v___x_2500_, v___x_2499_);
v___x_2503_ = l_Lean_MessageData_ofList(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2498_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = l_Lean_throwError___redArg(v_inst_2486_, v_inst_2487_, v___x_2504_);
return v___x_2505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_n_2512_, lean_object* v_cs_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_ensureNoOverload___redArg(v_inst_2510_, v_inst_2511_, v_n_2512_, v_cs_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_n_2517_, lean_object* v_____do__lift_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_ensureNoOverload___redArg(v_inst_2515_, v_inst_2516_, v_n_2517_, v_____do__lift_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_inst_2526_, lean_object* v_n_2527_){
_start:
{
lean_object* v_toBind_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_toBind_2528_ = lean_ctor_get(v_inst_2520_, 1);
lean_inc(v_toBind_2528_);
lean_inc(v_n_2527_);
lean_inc_ref(v_inst_2526_);
lean_inc_ref(v_inst_2520_);
v___f_2529_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2529_, 0, v_inst_2520_);
lean_closure_set(v___f_2529_, 1, v_inst_2526_);
lean_closure_set(v___f_2529_, 2, v_n_2527_);
v___x_2530_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2520_, v_inst_2521_, v_inst_2522_, v_inst_2523_, v_inst_2524_, v_inst_2525_, v_inst_2526_, v_n_2527_);
v___x_2531_ = lean_apply_4(v_toBind_2528_, lean_box(0), lean_box(0), v___x_2530_, v___f_2529_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_n_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2533_, v_inst_2534_, v_inst_2535_, v_inst_2536_, v_inst_2537_, v_inst_2538_, v_inst_2539_, v_n_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2542_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 1)
{
lean_object* v_fields_2543_; 
v_fields_2543_ = lean_ctor_get(v_x_2542_, 1);
if (lean_obj_tag(v_fields_2543_) == 0)
{
lean_object* v_n_2544_; lean_object* v___x_2545_; 
v_n_2544_ = lean_ctor_get(v_x_2542_, 0);
lean_inc(v_n_2544_);
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_n_2544_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_box(0);
return v___x_2546_;
}
}
else
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_box(0);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2548_);
lean_dec_ref(v_x_2548_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2550_, lean_object* v_withRef_2551_, lean_object* v___x_2552_, lean_object* v_oldRef_2553_){
_start:
{
lean_object* v_ref_2554_; lean_object* v___x_2555_; 
v_ref_2554_ = l_Lean_replaceRef(v_stx_2550_, v_oldRef_2553_);
v___x_2555_ = lean_apply_3(v_withRef_2551_, lean_box(0), v_ref_2554_, v___x_2552_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2556_, lean_object* v_withRef_2557_, lean_object* v___x_2558_, lean_object* v_oldRef_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2556_, v_withRef_2557_, v___x_2558_, v_oldRef_2559_);
lean_dec(v_oldRef_2559_);
lean_dec(v_stx_2556_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_stx_2564_, lean_object* v_k_2565_){
_start:
{
if (lean_obj_tag(v_stx_2564_) == 3)
{
lean_object* v_toApplicative_2566_; lean_object* v_toBind_2567_; lean_object* v_toPure_2568_; lean_object* v_toMonadRef_2569_; lean_object* v_val_2570_; lean_object* v_preresolved_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v_pre_2574_; uint8_t v___x_2575_; 
v_toApplicative_2566_ = lean_ctor_get(v_inst_2562_, 0);
lean_inc_ref(v_toApplicative_2566_);
v_toBind_2567_ = lean_ctor_get(v_inst_2562_, 1);
lean_inc(v_toBind_2567_);
lean_dec_ref(v_inst_2562_);
v_toPure_2568_ = lean_ctor_get(v_toApplicative_2566_, 1);
lean_inc(v_toPure_2568_);
lean_dec_ref(v_toApplicative_2566_);
v_toMonadRef_2569_ = lean_ctor_get(v_inst_2563_, 1);
lean_inc_ref(v_toMonadRef_2569_);
lean_dec_ref(v_inst_2563_);
v_val_2570_ = lean_ctor_get(v_stx_2564_, 2);
v_preresolved_2571_ = lean_ctor_get(v_stx_2564_, 3);
v___f_2572_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2573_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2571_);
v_pre_2574_ = l_List_filterMapTR_go___redArg(v___f_2572_, v_preresolved_2571_, v___x_2573_);
v___x_2575_ = l_List_isEmpty___redArg(v_pre_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
lean_dec_ref(v_toMonadRef_2569_);
lean_dec(v_toBind_2567_);
lean_dec_ref_known(v_stx_2564_, 4);
lean_dec(v_k_2565_);
v___x_2576_ = lean_apply_2(v_toPure_2568_, lean_box(0), v_pre_2574_);
return v___x_2576_;
}
else
{
lean_object* v_getRef_2577_; lean_object* v_withRef_2578_; lean_object* v___x_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; 
lean_dec(v_pre_2574_);
lean_dec(v_toPure_2568_);
v_getRef_2577_ = lean_ctor_get(v_toMonadRef_2569_, 0);
lean_inc(v_getRef_2577_);
v_withRef_2578_ = lean_ctor_get(v_toMonadRef_2569_, 1);
lean_inc(v_withRef_2578_);
lean_dec_ref(v_toMonadRef_2569_);
lean_inc(v_val_2570_);
v___x_2579_ = lean_apply_1(v_k_2565_, v_val_2570_);
v___f_2580_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2580_, 0, v_stx_2564_);
lean_closure_set(v___f_2580_, 1, v_withRef_2578_);
lean_closure_set(v___f_2580_, 2, v___x_2579_);
v___x_2581_ = lean_apply_4(v_toBind_2567_, lean_box(0), lean_box(0), v_getRef_2577_, v___f_2580_);
return v___x_2581_;
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v_k_2565_);
v___x_2582_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2583_ = l_Lean_throwErrorAt___redArg(v_inst_2562_, v_inst_2563_, v_stx_2564_, v___x_2582_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2584_, lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_stx_2587_, lean_object* v_k_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2585_, v_inst_2586_, v_stx_2587_, v_k_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_stx_2597_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_inc_ref(v_inst_2596_);
lean_inc_ref(v_inst_2590_);
v___x_2598_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2598_, 0, lean_box(0));
lean_closure_set(v___x_2598_, 1, v_inst_2590_);
lean_closure_set(v___x_2598_, 2, v_inst_2591_);
lean_closure_set(v___x_2598_, 3, v_inst_2592_);
lean_closure_set(v___x_2598_, 4, v_inst_2593_);
lean_closure_set(v___x_2598_, 5, v_inst_2594_);
lean_closure_set(v___x_2598_, 6, v_inst_2595_);
lean_closure_set(v___x_2598_, 7, v_inst_2596_);
v___x_2599_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2590_, v_inst_2596_, v_stx_2597_, v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_stx_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_resolveGlobalConst___redArg(v_inst_2601_, v_inst_2602_, v_inst_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v_stx_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2611_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2612_ = lean_unsigned_to_nat(11u);
v___x_2613_ = lean_unsigned_to_nat(456u);
v___x_2614_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2615_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2616_ = l_mkPanicMessageWithDecl(v___x_2615_, v___x_2614_, v___x_2613_, v___x_2612_, v___x_2611_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_id_2622_, lean_object* v_cs_2623_){
_start:
{
if (lean_obj_tag(v_cs_2623_) == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v_id_2622_);
lean_dec_ref(v_inst_2621_);
v___x_2624_ = lean_box(0);
v___x_2625_ = l_instInhabitedOfMonad___redArg(v_inst_2620_, v___x_2624_);
v___x_2626_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2627_ = l_panic___redArg(v___x_2625_, v___x_2626_);
lean_dec(v___x_2625_);
return v___x_2627_;
}
else
{
lean_object* v_tail_2628_; 
v_tail_2628_ = lean_ctor_get(v_cs_2623_, 1);
if (lean_obj_tag(v_tail_2628_) == 0)
{
lean_object* v_toApplicative_2629_; lean_object* v_toPure_2630_; lean_object* v_head_2631_; lean_object* v___x_2632_; 
v_toApplicative_2629_ = lean_ctor_get(v_inst_2620_, 0);
lean_inc_ref(v_toApplicative_2629_);
lean_dec(v_id_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec_ref(v_inst_2620_);
v_toPure_2630_ = lean_ctor_get(v_toApplicative_2629_, 1);
lean_inc(v_toPure_2630_);
lean_dec_ref(v_toApplicative_2629_);
v_head_2631_ = lean_ctor_get(v_cs_2623_, 0);
lean_inc(v_head_2631_);
lean_dec_ref_known(v_cs_2623_, 2);
v___x_2632_ = lean_apply_2(v_toPure_2630_, lean_box(0), v_head_2631_);
return v___x_2632_;
}
else
{
lean_object* v___f_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___f_2633_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2634_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2635_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2636_ = lean_box(0);
v___x_2637_ = 0;
lean_inc(v_id_2622_);
v___x_2638_ = l_Lean_Syntax_formatStx(v_id_2622_, v___x_2636_, v___x_2637_);
v___x_2639_ = l_Std_Format_defWidth;
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = l_Std_Format_pretty(v___x_2638_, v___x_2639_, v___x_2640_, v___x_2640_);
v___x_2642_ = lean_string_append(v___x_2635_, v___x_2641_);
lean_dec_ref(v___x_2641_);
v___x_2643_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2644_ = lean_string_append(v___x_2642_, v___x_2643_);
v___x_2645_ = lean_box(0);
v___x_2646_ = l_List_mapTR_loop___redArg(v___f_2633_, v_cs_2623_, v___x_2645_);
v___x_2647_ = l_List_toString___redArg(v___x_2634_, v___x_2646_);
v___x_2648_ = lean_string_append(v___x_2644_, v___x_2647_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
v___x_2650_ = l_Lean_MessageData_ofFormat(v___x_2649_);
v___x_2651_ = l_Lean_throwErrorAt___redArg(v_inst_2620_, v_inst_2621_, v_id_2622_, v___x_2650_);
return v___x_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_id_2655_, lean_object* v_cs_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2653_, v_inst_2654_, v_id_2655_, v_cs_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_id_2660_, lean_object* v_____do__lift_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2658_, v_inst_2659_, v_id_2660_, v_____do__lift_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_id_2670_){
_start:
{
lean_object* v_toBind_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_toBind_2671_ = lean_ctor_get(v_inst_2663_, 1);
lean_inc(v_toBind_2671_);
lean_inc(v_id_2670_);
lean_inc_ref(v_inst_2669_);
lean_inc_ref(v_inst_2663_);
v___f_2672_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2672_, 0, v_inst_2663_);
lean_closure_set(v___f_2672_, 1, v_inst_2669_);
lean_closure_set(v___f_2672_, 2, v_id_2670_);
v___x_2673_ = l_Lean_resolveGlobalConst___redArg(v_inst_2663_, v_inst_2664_, v_inst_2665_, v_inst_2666_, v_inst_2667_, v_inst_2668_, v_inst_2669_, v_id_2670_);
v___x_2674_ = lean_apply_4(v_toBind_2671_, lean_box(0), lean_box(0), v___x_2673_, v___f_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_id_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_id_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v_fst_2685_, lean_object* v_snd_2686_, lean_object* v_toPure_2687_, lean_object* v_____r_2688_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2689_ = l_Lean_LocalDecl_toExpr(v_fst_2685_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_snd_2686_);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
v___x_2692_ = lean_apply_2(v_toPure_2687_, lean_box(0), v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_snd_2693_, lean_object* v_x_2694_){
_start:
{
lean_object* v_snd_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v_snd_2695_ = lean_ctor_get(v_x_2694_, 1);
v___x_2696_ = l_List_lengthTR___redArg(v_snd_2695_);
v___x_2697_ = l_List_lengthTR___redArg(v_snd_2693_);
v___x_2698_ = lean_nat_dec_lt(v___x_2696_, v___x_2697_);
lean_dec(v___x_2697_);
lean_dec(v___x_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_snd_2699_, lean_object* v_x_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_snd_2699_, v_x_2700_);
lean_dec_ref(v_x_2700_);
lean_dec(v_snd_2699_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2(lean_object* v___f_2703_, lean_object* v___f_2704_, lean_object* v_toPure_2705_, lean_object* v_r_2706_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = l_List_any___redArg(v_r_2706_, v___f_2703_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_toPure_2705_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_apply_1(v___f_2704_, v___x_2708_);
return v___x_2709_;
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v___f_2704_);
v___x_2710_ = lean_box(0);
v___x_2711_ = lean_apply_2(v_toPure_2705_, lean_box(0), v___x_2710_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_view_2718_, lean_object* v_findLocalDecl_x3f_2719_, lean_object* v_n_2720_, lean_object* v_projs_2721_, lean_object* v_auxDecl_x3f_2722_){
_start:
{
lean_object* v_toApplicative_2723_; lean_object* v_toBind_2724_; lean_object* v_toPure_2725_; lean_object* v_auxDecl_x3f_2727_; lean_object* v_imported_2746_; lean_object* v_ctx_2747_; lean_object* v_scopes_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_toApplicative_2723_ = lean_ctor_get(v_inst_2712_, 0);
v_toBind_2724_ = lean_ctor_get(v_inst_2712_, 1);
v_toPure_2725_ = lean_ctor_get(v_toApplicative_2723_, 1);
v_imported_2746_ = lean_ctor_get(v_view_2718_, 1);
v_ctx_2747_ = lean_ctor_get(v_view_2718_, 2);
v_scopes_2748_ = lean_ctor_get(v_view_2718_, 3);
lean_inc(v_scopes_2748_);
lean_inc(v_ctx_2747_);
lean_inc(v_imported_2746_);
lean_inc(v_n_2720_);
v___x_2749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2749_, 0, v_n_2720_);
lean_ctor_set(v___x_2749_, 1, v_imported_2746_);
lean_ctor_set(v___x_2749_, 2, v_ctx_2747_);
lean_ctor_set(v___x_2749_, 3, v_scopes_2748_);
lean_inc_ref(v_findLocalDecl_x3f_2719_);
v___x_2750_ = lean_apply_1(v_findLocalDecl_x3f_2719_, v___x_2749_);
if (lean_obj_tag(v___x_2750_) == 1)
{
lean_object* v_val_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2774_; 
v_val_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2774_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_val_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2774_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
uint8_t v___x_2755_; 
v___x_2755_ = l_Lean_LocalDecl_isAuxDecl(v_val_2751_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2767_; 
lean_inc(v_toPure_2725_);
lean_dec(v_auxDecl_x3f_2722_);
lean_dec(v_n_2720_);
lean_dec_ref(v_findLocalDecl_x3f_2719_);
lean_dec_ref(v_view_2718_);
lean_dec(v_inst_2717_);
lean_dec_ref(v_inst_2716_);
lean_dec_ref(v_inst_2715_);
lean_dec_ref(v_inst_2714_);
lean_dec_ref(v_inst_2713_);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_inst_2712_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; lean_object* v_unused_2769_; 
v_unused_2768_ = lean_ctor_get(v_inst_2712_, 1);
lean_dec(v_unused_2768_);
v_unused_2769_ = lean_ctor_get(v_inst_2712_, 0);
lean_dec(v_unused_2769_);
v___x_2757_ = v_inst_2712_;
v_isShared_2758_ = v_isSharedCheck_2767_;
goto v_resetjp_2756_;
}
else
{
lean_dec(v_inst_2712_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2767_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = l_Lean_LocalDecl_toExpr(v_val_2751_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v_projs_2721_);
lean_ctor_set(v___x_2757_, 0, v___x_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_projs_2721_);
v___x_2761_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2763_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2761_);
v___x_2763_ = v___x_2753_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_apply_2(v_toPure_2725_, lean_box(0), v___x_2763_);
return v___x_2764_;
}
}
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_2722_) == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_inc(v_projs_2721_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_val_2751_);
lean_ctor_set(v___x_2770_, 1, v_projs_2721_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2770_);
v___x_2772_ = v___x_2753_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
v_auxDecl_x3f_2727_ = v___x_2772_;
goto v___jp_2726_;
}
}
else
{
lean_del_object(v___x_2753_);
lean_dec(v_val_2751_);
v_auxDecl_x3f_2727_ = v_auxDecl_x3f_2722_;
goto v___jp_2726_;
}
}
}
}
else
{
lean_dec(v___x_2750_);
v_auxDecl_x3f_2727_ = v_auxDecl_x3f_2722_;
goto v___jp_2726_;
}
v___jp_2726_:
{
if (lean_obj_tag(v_n_2720_) == 1)
{
lean_object* v_pre_2728_; lean_object* v_str_2729_; lean_object* v___x_2730_; 
v_pre_2728_ = lean_ctor_get(v_n_2720_, 0);
lean_inc(v_pre_2728_);
v_str_2729_ = lean_ctor_get(v_n_2720_, 1);
lean_inc_ref(v_str_2729_);
lean_dec_ref_known(v_n_2720_, 2);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_str_2729_);
lean_ctor_set(v___x_2730_, 1, v_projs_2721_);
v_n_2720_ = v_pre_2728_;
v_projs_2721_ = v___x_2730_;
v_auxDecl_x3f_2722_ = v_auxDecl_x3f_2727_;
goto _start;
}
else
{
lean_inc(v_toBind_2724_);
lean_dec(v_projs_2721_);
lean_dec(v_n_2720_);
lean_dec_ref(v_findLocalDecl_x3f_2719_);
if (lean_obj_tag(v_auxDecl_x3f_2727_) == 1)
{
lean_object* v_val_2732_; lean_object* v_fst_2733_; lean_object* v_snd_2734_; lean_object* v___f_2735_; uint8_t v___x_2736_; 
v_val_2732_ = lean_ctor_get(v_auxDecl_x3f_2727_, 0);
lean_inc(v_val_2732_);
lean_dec_ref_known(v_auxDecl_x3f_2727_, 1);
v_fst_2733_ = lean_ctor_get(v_val_2732_, 0);
lean_inc_n(v_fst_2733_, 2);
v_snd_2734_ = lean_ctor_get(v_val_2732_, 1);
lean_inc_n(v_snd_2734_, 2);
lean_dec(v_val_2732_);
lean_inc(v_toPure_2725_);
v___f_2735_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2735_, 0, v_fst_2733_);
lean_closure_set(v___f_2735_, 1, v_snd_2734_);
lean_closure_set(v___f_2735_, 2, v_toPure_2725_);
v___x_2736_ = l_List_isEmpty___redArg(v_snd_2734_);
if (v___x_2736_ == 0)
{
lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec(v_fst_2733_);
v___f_2737_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2737_, 0, v_snd_2734_);
lean_inc(v_toPure_2725_);
v___f_2738_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2738_, 0, v___f_2737_);
lean_closure_set(v___f_2738_, 1, v___f_2735_);
lean_closure_set(v___f_2738_, 2, v_toPure_2725_);
v___x_2739_ = l_Lean_MacroScopesView_review(v_view_2718_);
v___x_2740_ = l_Lean_resolveGlobalName___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_inst_2715_, v_inst_2716_, v_inst_2717_, v___x_2739_, v___x_2736_);
v___x_2741_ = lean_apply_4(v_toBind_2724_, lean_box(0), lean_box(0), v___x_2740_, v___f_2738_);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_inc(v_toPure_2725_);
lean_dec_ref(v___f_2735_);
lean_dec(v_toBind_2724_);
lean_dec_ref(v_view_2718_);
lean_dec(v_inst_2717_);
lean_dec_ref(v_inst_2716_);
lean_dec_ref(v_inst_2715_);
lean_dec_ref(v_inst_2714_);
lean_dec_ref(v_inst_2713_);
lean_dec_ref(v_inst_2712_);
v___x_2742_ = lean_box(0);
v___x_2743_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v_fst_2733_, v_snd_2734_, v_toPure_2725_, v___x_2742_);
return v___x_2743_;
}
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_inc(v_toPure_2725_);
lean_dec(v_auxDecl_x3f_2727_);
lean_dec(v_toBind_2724_);
lean_dec_ref(v_view_2718_);
lean_dec(v_inst_2717_);
lean_dec_ref(v_inst_2716_);
lean_dec_ref(v_inst_2715_);
lean_dec_ref(v_inst_2714_);
lean_dec_ref(v_inst_2713_);
lean_dec_ref(v_inst_2712_);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_apply_2(v_toPure_2725_, lean_box(0), v___x_2744_);
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_view_2782_, lean_object* v_findLocalDecl_x3f_2783_, lean_object* v_n_2784_, lean_object* v_projs_2785_, lean_object* v_auxDecl_x3f_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2776_, v_inst_2777_, v_inst_2778_, v_inst_2779_, v_inst_2780_, v_inst_2781_, v_view_2782_, v_findLocalDecl_x3f_2783_, v_n_2784_, v_projs_2785_, v_auxDecl_x3f_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2788_, lean_object* v_givenNameView_2789_, lean_object* v_fullDeclName_2790_, lean_object* v_ns_2791_){
_start:
{
lean_object* v_name_2792_; lean_object* v_imported_2793_; lean_object* v_ctx_2794_; lean_object* v_scopes_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v_name_2792_ = lean_ctor_get(v_givenNameView_2789_, 0);
v_imported_2793_ = lean_ctor_get(v_givenNameView_2789_, 1);
v_ctx_2794_ = lean_ctor_get(v_givenNameView_2789_, 2);
v_scopes_2795_ = lean_ctor_get(v_givenNameView_2789_, 3);
lean_inc(v_name_2792_);
lean_inc(v_ns_2791_);
v___x_2796_ = l_Lean_Name_append(v_ns_2791_, v_name_2792_);
lean_inc(v_scopes_2795_);
lean_inc(v_ctx_2794_);
lean_inc(v_imported_2793_);
v___x_2797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v_imported_2793_);
lean_ctor_set(v___x_2797_, 2, v_ctx_2794_);
lean_ctor_set(v___x_2797_, 3, v_scopes_2795_);
v___x_2798_ = l_Lean_MacroScopesView_review(v___x_2797_);
v___x_2799_ = lean_name_eq(v___x_2798_, v_fullDeclName_2790_);
lean_dec(v___x_2798_);
if (v___x_2799_ == 0)
{
if (lean_obj_tag(v_ns_2791_) == 1)
{
lean_object* v_pre_2800_; 
v_pre_2800_ = lean_ctor_get(v_ns_2791_, 0);
lean_inc(v_pre_2800_);
lean_dec_ref_known(v_ns_2791_, 2);
v_ns_2791_ = v_pre_2800_;
goto _start;
}
else
{
lean_object* v___x_2802_; 
lean_dec(v_ns_2791_);
lean_dec_ref(v_givenNameView_2789_);
lean_dec_ref(v_localDecl_2788_);
v___x_2802_ = lean_box(0);
return v___x_2802_;
}
}
else
{
lean_object* v___x_2803_; 
lean_dec(v_ns_2791_);
lean_dec_ref(v_givenNameView_2789_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_localDecl_2788_);
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2804_, lean_object* v_givenNameView_2805_, lean_object* v_fullDeclName_2806_, lean_object* v_ns_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2804_, v_givenNameView_2805_, v_fullDeclName_2806_, v_ns_2807_);
lean_dec(v_fullDeclName_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2809_, lean_object* v_givenName_2810_){
_start:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = l_Lean_LocalDecl_userName(v_localDecl_2809_);
v___x_2812_ = lean_name_eq(v___x_2811_, v_givenName_2810_);
lean_dec(v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
lean_dec_ref(v_localDecl_2809_);
v___x_2813_ = lean_box(0);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_localDecl_2809_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2815_, lean_object* v_givenName_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2815_, v_givenName_2816_);
lean_dec(v_givenName_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2818_, lean_object* v_givenName_2819_, lean_object* v___f_2820_, lean_object* v_auxDeclToFullName_2821_, lean_object* v_currNamespace_2822_, lean_object* v_givenNameView_2823_, lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_dec_ref(v_givenNameView_2823_);
lean_dec(v_currNamespace_2822_);
lean_dec(v_auxDeclToFullName_2821_);
lean_dec_ref(v___f_2820_);
lean_dec(v_givenName_2819_);
lean_dec_ref(v_matchLocalDecl_x3f_2818_);
return v_x_2824_;
}
else
{
lean_object* v_val_2825_; uint8_t v___x_2826_; 
v_val_2825_ = lean_ctor_get(v_x_2824_, 0);
v___x_2826_ = l_Lean_LocalDecl_isAuxDecl(v_val_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
lean_inc(v_val_2825_);
lean_dec_ref_known(v_x_2824_, 1);
lean_dec_ref(v_givenNameView_2823_);
lean_dec(v_currNamespace_2822_);
lean_dec(v_auxDeclToFullName_2821_);
lean_dec_ref(v___f_2820_);
v___x_2827_ = lean_apply_2(v_matchLocalDecl_x3f_2818_, v_val_2825_, v_givenName_2819_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = l_Lean_LocalDecl_fvarId(v_val_2825_);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2820_, v_auxDeclToFullName_2821_, v___x_2828_);
if (lean_obj_tag(v___x_2829_) == 1)
{
lean_object* v_val_2830_; lean_object* v_fullDeclView_2831_; lean_object* v_name_2832_; lean_object* v_imported_2833_; lean_object* v_ctx_2834_; lean_object* v_scopes_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_givenName_2819_);
lean_dec_ref(v_matchLocalDecl_x3f_2818_);
v_val_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v_fullDeclView_2831_ = l_Lean_extractMacroScopes(v_val_2830_);
v_name_2832_ = lean_ctor_get(v_fullDeclView_2831_, 0);
v_imported_2833_ = lean_ctor_get(v_fullDeclView_2831_, 1);
v_ctx_2834_ = lean_ctor_get(v_fullDeclView_2831_, 2);
v_scopes_2835_ = lean_ctor_get(v_fullDeclView_2831_, 3);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_fullDeclView_2831_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2837_ = v_fullDeclView_2831_;
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_scopes_2835_);
lean_inc(v_ctx_2834_);
lean_inc(v_imported_2833_);
lean_inc(v_name_2832_);
lean_dec(v_fullDeclView_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___y_2840_; lean_object* v___x_2853_; 
lean_inc(v_name_2832_);
v___x_2853_ = l_Lean_privateToUserName_x3f(v_name_2832_);
if (lean_obj_tag(v___x_2853_) == 0)
{
v___y_2840_ = v_name_2832_;
goto v___jp_2839_;
}
else
{
lean_object* v_val_2854_; 
lean_dec(v_name_2832_);
v_val_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___y_2840_ = v_val_2854_;
goto v___jp_2839_;
}
v___jp_2839_:
{
lean_object* v_fullDeclView_2842_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___y_2840_);
v_fullDeclView_2842_ = v___x_2837_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___y_2840_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_imported_2833_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_ctx_2834_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_scopes_2835_);
v_fullDeclView_2842_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v_fullDeclName_2843_; uint8_t v___x_2844_; 
lean_inc_ref(v_fullDeclView_2842_);
v_fullDeclName_2843_ = l_Lean_MacroScopesView_review(v_fullDeclView_2842_);
v___x_2844_ = l_Lean_Name_isPrefixOf(v_currNamespace_2822_, v_fullDeclName_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_inc(v_val_2825_);
lean_dec_ref(v_fullDeclView_2842_);
lean_dec_ref_known(v_x_2824_, 1);
v___x_2845_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2825_, v_givenNameView_2823_, v_fullDeclName_2843_, v_currNamespace_2822_);
lean_dec(v_fullDeclName_2843_);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; lean_object* v_localDeclNameView_2847_; uint8_t v___x_2848_; 
lean_dec(v_fullDeclName_2843_);
lean_dec(v_currNamespace_2822_);
v___x_2846_ = l_Lean_LocalDecl_userName(v_val_2825_);
v_localDeclNameView_2847_ = l_Lean_extractMacroScopes(v___x_2846_);
v___x_2848_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2847_, v_givenNameView_2823_);
lean_dec_ref(v_localDeclNameView_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v_fullDeclView_2842_);
lean_dec_ref_known(v_x_2824_, 1);
lean_dec_ref(v_givenNameView_2823_);
v___x_2849_ = lean_box(0);
return v___x_2849_;
}
else
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2823_, v_fullDeclView_2842_);
lean_dec_ref(v_fullDeclView_2842_);
lean_dec_ref(v_givenNameView_2823_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref_known(v_x_2824_, 1);
v___x_2851_ = lean_box(0);
return v___x_2851_;
}
else
{
return v_x_2824_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2856_; 
lean_inc(v_val_2825_);
lean_dec(v___x_2829_);
lean_dec_ref_known(v_x_2824_, 1);
lean_dec_ref(v_givenNameView_2823_);
lean_dec(v_currNamespace_2822_);
v___x_2856_ = lean_apply_2(v_matchLocalDecl_x3f_2818_, v_val_2825_, v_givenName_2819_);
return v___x_2856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2857_, lean_object* v_matchLocalDecl_x3f_2858_, lean_object* v_givenName_2859_, lean_object* v_x_2860_){
_start:
{
if (lean_obj_tag(v_x_2860_) == 0)
{
lean_dec(v_givenName_2859_);
lean_dec_ref(v_matchLocalDecl_x3f_2858_);
return v_x_2860_;
}
else
{
lean_object* v_val_2861_; uint8_t v___x_2862_; 
v_val_2861_ = lean_ctor_get(v_x_2860_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v_x_2860_, 1);
v___x_2862_ = l_Lean_LocalDecl_isAuxDecl(v_val_2861_);
if (v___x_2862_ == 0)
{
lean_dec(v_val_2861_);
lean_dec(v_givenName_2859_);
lean_dec_ref(v_matchLocalDecl_x3f_2858_);
lean_inc(v_localDecl_x3f_2857_);
return v_localDecl_x3f_2857_;
}
else
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_apply_2(v_matchLocalDecl_x3f_2858_, v_val_2861_, v_givenName_2859_);
return v___x_2863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2864_, lean_object* v_matchLocalDecl_x3f_2865_, lean_object* v_givenName_2866_, lean_object* v_x_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2864_, v_matchLocalDecl_x3f_2865_, v_givenName_2866_, v_x_2867_);
lean_dec(v_localDecl_x3f_2864_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2888_, lean_object* v_matchLocalDecl_x3f_2889_, lean_object* v___f_2890_, lean_object* v_auxDeclToFullName_2891_, lean_object* v_currNamespace_2892_, lean_object* v_givenNameView_2893_){
_start:
{
lean_object* v_decls_2894_; lean_object* v_givenName_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v_localDecl_x3f_2898_; 
v_decls_2894_ = lean_ctor_get(v_lctx_2888_, 1);
lean_inc_ref_n(v_decls_2894_, 2);
lean_dec_ref(v_lctx_2888_);
lean_inc_ref(v_givenNameView_2893_);
v_givenName_2895_ = l_Lean_MacroScopesView_review(v_givenNameView_2893_);
lean_inc(v_givenName_2895_);
lean_inc_ref(v_matchLocalDecl_x3f_2889_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2896_, 0, v_matchLocalDecl_x3f_2889_);
lean_closure_set(v___f_2896_, 1, v_givenName_2895_);
lean_closure_set(v___f_2896_, 2, v___f_2890_);
lean_closure_set(v___f_2896_, 3, v_auxDeclToFullName_2891_);
lean_closure_set(v___f_2896_, 4, v_currNamespace_2892_);
lean_closure_set(v___f_2896_, 5, v_givenNameView_2893_);
v___x_2897_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2898_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2897_, v_decls_2894_, v___f_2896_);
if (lean_obj_tag(v_localDecl_x3f_2898_) == 0)
{
lean_object* v___f_2899_; lean_object* v___x_2900_; 
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2899_, 0, v_localDecl_x3f_2898_);
lean_closure_set(v___f_2899_, 1, v_matchLocalDecl_x3f_2889_);
lean_closure_set(v___f_2899_, 2, v_givenName_2895_);
v___x_2900_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2897_, v_decls_2894_, v___f_2899_);
return v___x_2900_;
}
else
{
lean_dec(v_givenName_2895_);
lean_dec_ref(v_decls_2894_);
lean_dec_ref(v_matchLocalDecl_x3f_2889_);
return v_localDecl_x3f_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2901_, lean_object* v_lctx_2902_, lean_object* v_matchLocalDecl_x3f_2903_, lean_object* v___f_2904_, lean_object* v_auxDeclToFullName_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_currNamespace_2912_){
_start:
{
lean_object* v_view_2913_; lean_object* v_name_2914_; lean_object* v_findLocalDecl_x3f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_view_2913_ = l_Lean_extractMacroScopes(v_n_2901_);
v_name_2914_ = lean_ctor_get(v_view_2913_, 0);
lean_inc(v_name_2914_);
v_findLocalDecl_x3f_2915_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3), 6, 5);
lean_closure_set(v_findLocalDecl_x3f_2915_, 0, v_lctx_2902_);
lean_closure_set(v_findLocalDecl_x3f_2915_, 1, v_matchLocalDecl_x3f_2903_);
lean_closure_set(v_findLocalDecl_x3f_2915_, 2, v___f_2904_);
lean_closure_set(v_findLocalDecl_x3f_2915_, 3, v_auxDeclToFullName_2905_);
lean_closure_set(v_findLocalDecl_x3f_2915_, 4, v_currNamespace_2912_);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_box(0);
v___x_2918_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2906_, v_inst_2907_, v_inst_2908_, v_inst_2909_, v_inst_2910_, v_inst_2911_, v_view_2913_, v_findLocalDecl_x3f_2915_, v_name_2914_, v___x_2916_, v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2919_, lean_object* v_n_2920_, lean_object* v_lctx_2921_, lean_object* v_matchLocalDecl_x3f_2922_, lean_object* v___f_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_toBind_2929_, lean_object* v_____do__lift_2930_){
_start:
{
lean_object* v_auxDeclToFullName_2931_; lean_object* v_getCurrNamespace_2932_; lean_object* v___f_2933_; lean_object* v___x_2934_; 
v_auxDeclToFullName_2931_ = lean_ctor_get(v_____do__lift_2930_, 2);
lean_inc(v_auxDeclToFullName_2931_);
lean_dec_ref(v_____do__lift_2930_);
v_getCurrNamespace_2932_ = lean_ctor_get(v_inst_2919_, 0);
lean_inc(v_getCurrNamespace_2932_);
v___f_2933_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2933_, 0, v_n_2920_);
lean_closure_set(v___f_2933_, 1, v_lctx_2921_);
lean_closure_set(v___f_2933_, 2, v_matchLocalDecl_x3f_2922_);
lean_closure_set(v___f_2933_, 3, v___f_2923_);
lean_closure_set(v___f_2933_, 4, v_auxDeclToFullName_2931_);
lean_closure_set(v___f_2933_, 5, v_inst_2924_);
lean_closure_set(v___f_2933_, 6, v_inst_2919_);
lean_closure_set(v___f_2933_, 7, v_inst_2925_);
lean_closure_set(v___f_2933_, 8, v_inst_2926_);
lean_closure_set(v___f_2933_, 9, v_inst_2927_);
lean_closure_set(v___f_2933_, 10, v_inst_2928_);
v___x_2934_ = lean_apply_4(v_toBind_2929_, lean_box(0), lean_box(0), v_getCurrNamespace_2932_, v___f_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2935_, lean_object* v_n_2936_, lean_object* v_matchLocalDecl_x3f_2937_, lean_object* v___f_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_toBind_2944_, lean_object* v_inst_2945_, lean_object* v_lctx_2946_){
_start:
{
lean_object* v___f_2947_; lean_object* v___x_2948_; 
lean_inc(v_toBind_2944_);
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2947_, 0, v_inst_2935_);
lean_closure_set(v___f_2947_, 1, v_n_2936_);
lean_closure_set(v___f_2947_, 2, v_lctx_2946_);
lean_closure_set(v___f_2947_, 3, v_matchLocalDecl_x3f_2937_);
lean_closure_set(v___f_2947_, 4, v___f_2938_);
lean_closure_set(v___f_2947_, 5, v_inst_2939_);
lean_closure_set(v___f_2947_, 6, v_inst_2940_);
lean_closure_set(v___f_2947_, 7, v_inst_2941_);
lean_closure_set(v___f_2947_, 8, v_inst_2942_);
lean_closure_set(v___f_2947_, 9, v_inst_2943_);
lean_closure_set(v___f_2947_, 10, v_toBind_2944_);
v___x_2948_ = lean_apply_4(v_toBind_2944_, lean_box(0), lean_box(0), v_inst_2945_, v___f_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_n_2958_){
_start:
{
lean_object* v_toBind_2959_; lean_object* v___f_2960_; lean_object* v_matchLocalDecl_x3f_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; 
v_toBind_2959_ = lean_ctor_get(v_inst_2951_, 1);
lean_inc_n(v_toBind_2959_, 2);
v___f_2960_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2961_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2957_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2962_, 0, v_inst_2952_);
lean_closure_set(v___f_2962_, 1, v_n_2958_);
lean_closure_set(v___f_2962_, 2, v_matchLocalDecl_x3f_2961_);
lean_closure_set(v___f_2962_, 3, v___f_2960_);
lean_closure_set(v___f_2962_, 4, v_inst_2951_);
lean_closure_set(v___f_2962_, 5, v_inst_2953_);
lean_closure_set(v___f_2962_, 6, v_inst_2954_);
lean_closure_set(v___f_2962_, 7, v_inst_2955_);
lean_closure_set(v___f_2962_, 8, v_inst_2956_);
lean_closure_set(v___f_2962_, 9, v_toBind_2959_);
lean_closure_set(v___f_2962_, 10, v_inst_2957_);
v___x_2963_ = lean_apply_4(v_toBind_2959_, lean_box(0), lean_box(0), v_inst_2957_, v___f_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2964_, lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_n_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_resolveLocalName___redArg(v_inst_2965_, v_inst_2966_, v_inst_2967_, v_inst_2968_, v_inst_2969_, v_inst_2970_, v_inst_2971_, v_n_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2974_, uint8_t v_____do__lift_2975_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = lean_box(v_____do__lift_2975_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___x_2978_ = lean_apply_2(v_toPure_2974_, lean_box(0), v___x_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2979_, lean_object* v_____do__lift_2980_){
_start:
{
uint8_t v_____do__lift_1060__boxed_2981_; lean_object* v_res_2982_; 
v_____do__lift_1060__boxed_2981_ = lean_unbox(v_____do__lift_2980_);
v_res_2982_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2979_, v_____do__lift_1060__boxed_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2983_, lean_object* v___y_2984_, lean_object* v_____do__lift_2985_){
_start:
{
if (lean_obj_tag(v_____do__lift_2985_) == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v___y_2984_);
v___x_2986_ = lean_box(0);
v___x_2987_ = lean_apply_2(v_toPure_2983_, lean_box(0), v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2995_; 
v_isSharedCheck_2995_ = !lean_is_exclusive(v_____do__lift_2985_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v_____do__lift_2985_, 0);
lean_dec(v_unused_2996_);
v___x_2989_ = v_____do__lift_2985_;
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v_____do__lift_2985_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___y_2984_);
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___y_2984_);
v___x_2992_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_apply_2(v_toPure_2983_, lean_box(0), v___x_2992_);
return v___x_2993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2999_, lean_object* v_toBind_3000_, lean_object* v___f_3001_, lean_object* v_____do__lift_3002_){
_start:
{
if (lean_obj_tag(v_____do__lift_3002_) == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v___f_3001_);
lean_dec(v_toBind_3000_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_apply_2(v_toPure_2999_, lean_box(0), v___x_3003_);
return v___x_3004_;
}
else
{
lean_object* v_val_3005_; uint8_t v___x_3006_; 
v_val_3005_ = lean_ctor_get(v_____do__lift_3002_, 0);
v___x_3006_ = lean_unbox(v_val_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_apply_2(v_toPure_2999_, lean_box(0), v___x_3007_);
v___x_3009_ = lean_apply_4(v_toBind_3000_, lean_box(0), lean_box(0), v___x_3008_, v___f_3001_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3011_ = lean_apply_2(v_toPure_2999_, lean_box(0), v___x_3010_);
v___x_3012_ = lean_apply_4(v_toBind_3000_, lean_box(0), lean_box(0), v___x_3011_, v___f_3001_);
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_3013_, lean_object* v_toBind_3014_, lean_object* v___f_3015_, lean_object* v_____do__lift_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_3013_, v_toBind_3014_, v___f_3015_, v_____do__lift_3016_);
lean_dec(v_____do__lift_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_3018_, lean_object* v_filter_3019_, lean_object* v___y_3020_, lean_object* v_toBind_3021_, lean_object* v___f_3022_, lean_object* v___f_3023_, lean_object* v_____do__lift_3024_){
_start:
{
if (lean_obj_tag(v_____do__lift_3024_) == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec(v___f_3023_);
lean_dec(v___f_3022_);
lean_dec(v_toBind_3021_);
lean_dec(v___y_3020_);
lean_dec(v_filter_3019_);
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_apply_2(v_toPure_3018_, lean_box(0), v___x_3025_);
return v___x_3026_;
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec(v_toPure_3018_);
v___x_3027_ = lean_apply_1(v_filter_3019_, v___y_3020_);
lean_inc(v_toBind_3021_);
v___x_3028_ = lean_apply_4(v_toBind_3021_, lean_box(0), lean_box(0), v___x_3027_, v___f_3022_);
v___x_3029_ = lean_apply_4(v_toBind_3021_, lean_box(0), lean_box(0), v___x_3028_, v___f_3023_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3030_, lean_object* v_filter_3031_, lean_object* v___y_3032_, lean_object* v_toBind_3033_, lean_object* v___f_3034_, lean_object* v___f_3035_, lean_object* v_____do__lift_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3030_, v_filter_3031_, v___y_3032_, v_toBind_3033_, v___f_3034_, v___f_3035_, v_____do__lift_3036_);
lean_dec(v_____do__lift_3036_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3038_, lean_object* v_n_u2080_3039_, lean_object* v_toBind_3040_, lean_object* v___f_3041_, lean_object* v_____do__lift_3042_){
_start:
{
if (lean_obj_tag(v_____do__lift_3042_) == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_dec(v___f_3041_);
lean_dec(v_toBind_3040_);
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_apply_2(v_toPure_3038_, lean_box(0), v___x_3046_);
return v___x_3047_;
}
else
{
lean_object* v_val_3048_; 
v_val_3048_ = lean_ctor_get(v_____do__lift_3042_, 0);
if (lean_obj_tag(v_val_3048_) == 1)
{
lean_object* v_tail_3049_; 
v_tail_3049_ = lean_ctor_get(v_val_3048_, 1);
if (lean_obj_tag(v_tail_3049_) == 0)
{
lean_object* v_head_3050_; lean_object* v_fst_3051_; uint8_t v___x_3052_; 
v_head_3050_ = lean_ctor_get(v_val_3048_, 0);
v_fst_3051_ = lean_ctor_get(v_head_3050_, 0);
v___x_3052_ = lean_name_eq(v_fst_3051_, v_n_u2080_3039_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
v___x_3054_ = lean_apply_2(v_toPure_3038_, lean_box(0), v___x_3053_);
v___x_3055_ = lean_apply_4(v_toBind_3040_, lean_box(0), lean_box(0), v___x_3054_, v___f_3041_);
return v___x_3055_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3057_ = lean_apply_2(v_toPure_3038_, lean_box(0), v___x_3056_);
v___x_3058_ = lean_apply_4(v_toBind_3040_, lean_box(0), lean_box(0), v___x_3057_, v___f_3041_);
return v___x_3058_;
}
}
else
{
lean_dec(v___f_3041_);
lean_dec(v_toBind_3040_);
goto v___jp_3043_;
}
}
else
{
lean_dec(v___f_3041_);
lean_dec(v_toBind_3040_);
goto v___jp_3043_;
}
}
v___jp_3043_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = lean_box(0);
v___x_3045_ = lean_apply_2(v_toPure_3038_, lean_box(0), v___x_3044_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3059_, lean_object* v_n_u2080_3060_, lean_object* v_toBind_3061_, lean_object* v___f_3062_, lean_object* v_____do__lift_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3059_, v_n_u2080_3060_, v_toBind_3061_, v___f_3062_, v_____do__lift_3063_);
lean_dec(v_____do__lift_3063_);
lean_dec(v_n_u2080_3060_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3065_, lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_n_u2080_3071_, lean_object* v_filter_3072_, lean_object* v_view_x3f_3073_, lean_object* v_n_3074_){
_start:
{
lean_object* v___f_3075_; lean_object* v___f_3076_; lean_object* v___f_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_toApplicative_3087_; lean_object* v_getEnv_3088_; lean_object* v_modifyEnv_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3127_; 
lean_inc_ref_n(v_inst_3065_, 8);
v___f_3075_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3075_, 0, v_inst_3065_);
v___f_3076_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3076_, 0, v_inst_3065_);
v___f_3077_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3077_, 0, v_inst_3065_);
v___f_3078_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3078_, 0, v_inst_3065_);
v___f_3079_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3079_, 0, v_inst_3065_);
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___f_3075_);
lean_ctor_set(v___x_3080_, 1, v___f_3076_);
v___x_3081_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3081_, 0, lean_box(0));
lean_closure_set(v___x_3081_, 1, v_inst_3065_);
v___x_3082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
lean_ctor_set(v___x_3082_, 2, v___f_3077_);
lean_ctor_set(v___x_3082_, 3, v___f_3078_);
lean_ctor_set(v___x_3082_, 4, v___f_3079_);
v___x_3083_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3083_, 0, lean_box(0));
lean_closure_set(v___x_3083_, 1, v_inst_3065_);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3085_, 0, lean_box(0));
lean_closure_set(v___x_3085_, 1, v_inst_3065_);
lean_inc_ref(v___x_3085_);
v___x_3086_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3085_, v_inst_3066_);
v_toApplicative_3087_ = lean_ctor_get(v_inst_3065_, 0);
lean_inc_ref(v_toApplicative_3087_);
v_getEnv_3088_ = lean_ctor_get(v_inst_3067_, 0);
v_modifyEnv_3089_ = lean_ctor_get(v_inst_3067_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_inst_3067_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3091_ = v_inst_3067_;
v_isShared_3092_ = v_isSharedCheck_3127_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_modifyEnv_3089_);
lean_inc(v_getEnv_3088_);
lean_dec(v_inst_3067_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3127_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v_toBind_3093_; lean_object* v_toPure_3094_; lean_object* v___f_3095_; lean_object* v___f_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v_toBind_3093_ = lean_ctor_get(v_inst_3065_, 1);
lean_inc_n(v_toBind_3093_, 2);
lean_dec_ref(v_inst_3065_);
v_toPure_3094_ = lean_ctor_get(v_toApplicative_3087_, 1);
lean_inc_n(v_toPure_3094_, 3);
lean_dec_ref(v_toApplicative_3087_);
lean_inc_ref(v___x_3085_);
v___f_3095_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3095_, 0, v_modifyEnv_3089_);
lean_closure_set(v___f_3095_, 1, v___x_3085_);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3096_, 0, v_toPure_3094_);
v___f_3097_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3097_, 0, v_toPure_3094_);
v___x_3098_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v_getEnv_3088_, v___f_3097_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___f_3095_);
lean_ctor_set(v___x_3091_, 0, v___x_3098_);
v___x_3100_ = v___x_3091_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___f_3095_);
v___x_3100_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___y_3105_; 
lean_inc_ref_n(v___x_3085_, 2);
v___x_3101_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_3085_, v_inst_3068_);
v___x_3102_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3085_, v_inst_3069_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3103_, 0, v_inst_3070_);
lean_closure_set(v___f_3103_, 1, v___x_3085_);
if (lean_obj_tag(v_view_x3f_3073_) == 1)
{
lean_object* v_val_3113_; lean_object* v_imported_3114_; lean_object* v_ctx_3115_; lean_object* v_scopes_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3124_; 
v_val_3113_ = lean_ctor_get(v_view_x3f_3073_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v_view_x3f_3073_, 1);
v_imported_3114_ = lean_ctor_get(v_val_3113_, 1);
v_ctx_3115_ = lean_ctor_get(v_val_3113_, 2);
v_scopes_3116_ = lean_ctor_get(v_val_3113_, 3);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_val_3113_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_val_3113_, 0);
lean_dec(v_unused_3125_);
v___x_3118_ = v_val_3113_;
v_isShared_3119_ = v_isSharedCheck_3124_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_scopes_3116_);
lean_inc(v_ctx_3115_);
lean_inc(v_imported_3114_);
lean_dec(v_val_3113_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3124_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v_n_3074_);
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_n_3074_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_imported_3114_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_ctx_3115_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_scopes_3116_);
v___x_3121_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Lean_MacroScopesView_review(v___x_3121_);
v___y_3105_ = v___x_3122_;
goto v___jp_3104_;
}
}
}
else
{
lean_dec(v_view_x3f_3073_);
v___y_3105_ = v_n_3074_;
goto v___jp_3104_;
}
v___jp_3104_:
{
lean_object* v___f_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___f_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_inc_n(v___y_3105_, 2);
lean_inc_n(v_toPure_3094_, 3);
v___f_3106_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3106_, 0, v_toPure_3094_);
lean_closure_set(v___f_3106_, 1, v___y_3105_);
lean_inc_n(v_toBind_3093_, 3);
v___f_3107_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3107_, 0, v_toPure_3094_);
lean_closure_set(v___f_3107_, 1, v_toBind_3093_);
lean_closure_set(v___f_3107_, 2, v___f_3106_);
v___f_3108_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3108_, 0, v_toPure_3094_);
lean_closure_set(v___f_3108_, 1, v_filter_3072_);
lean_closure_set(v___f_3108_, 2, v___y_3105_);
lean_closure_set(v___f_3108_, 3, v_toBind_3093_);
lean_closure_set(v___f_3108_, 4, v___f_3096_);
lean_closure_set(v___f_3108_, 5, v___f_3107_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3109_, 0, v_toPure_3094_);
lean_closure_set(v___f_3109_, 1, v_n_u2080_3071_);
lean_closure_set(v___f_3109_, 2, v_toBind_3093_);
lean_closure_set(v___f_3109_, 3, v___f_3108_);
v___x_3110_ = 0;
v___x_3111_ = l_Lean_resolveGlobalName___redArg(v___x_3084_, v___x_3086_, v___x_3100_, v___x_3101_, v___x_3102_, v___f_3103_, v___y_3105_, v___x_3110_);
v___x_3112_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v___x_3111_, v___f_3109_);
return v___x_3112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3128_, lean_object* v_inst_3129_, lean_object* v_inst_3130_, lean_object* v_inst_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_n_u2080_3135_, lean_object* v_filter_3136_, lean_object* v_view_x3f_3137_, lean_object* v_n_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3129_, v_inst_3130_, v_inst_3131_, v_inst_3132_, v_inst_3133_, v_inst_3134_, v_n_u2080_3135_, v_filter_3136_, v_view_x3f_3137_, v_n_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3140_, lean_object* v_____do__lift_3141_){
_start:
{
if (lean_obj_tag(v_____do__lift_3141_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3142_);
return v___x_3143_;
}
else
{
lean_object* v_val_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3152_; 
v_val_3144_ = lean_ctor_get(v_____do__lift_3141_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_____do__lift_3141_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3146_ = v_____do__lift_3141_;
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_val_3144_);
lean_dec(v_____do__lift_3141_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_val_3144_);
v___x_3149_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3149_);
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3157_, lean_object* v_____x_3158_){
_start:
{
if (lean_obj_tag(v_____x_3158_) == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1___closed__1));
v___x_3160_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3159_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_apply_2(v_toPure_3157_, lean_box(0), v_____x_3158_);
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3162_, lean_object* v_____do__lift_3163_){
_start:
{
if (lean_obj_tag(v_____do__lift_3163_) == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_box(0);
v___x_3165_ = lean_apply_2(v_toPure_3162_, lean_box(0), v___x_3164_);
return v___x_3165_;
}
else
{
lean_object* v_val_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3175_; 
v_val_3166_ = lean_ctor_get(v_____do__lift_3163_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_____do__lift_3163_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3168_ = v_____do__lift_3163_;
v_isShared_3169_ = v_isSharedCheck_3175_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_val_3166_);
lean_dec(v_____do__lift_3163_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3175_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v_val_3166_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_apply_2(v_toPure_3162_, lean_box(0), v___x_3172_);
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3176_, lean_object* v___x_3177_, lean_object* v_____do__lift_3178_){
_start:
{
if (lean_obj_tag(v_____do__lift_3178_) == 0)
{
lean_object* v___x_3179_; 
v___x_3179_ = lean_apply_2(v_toPure_3176_, lean_box(0), v___x_3177_);
return v___x_3179_;
}
else
{
lean_object* v_val_3180_; lean_object* v_fst_3181_; lean_object* v___x_3182_; 
lean_dec(v___x_3177_);
v_val_3180_ = lean_ctor_get(v_____do__lift_3178_, 0);
lean_inc(v_val_3180_);
lean_dec_ref_known(v_____do__lift_3178_, 1);
v_fst_3181_ = lean_ctor_get(v_val_3180_, 0);
lean_inc(v_fst_3181_);
lean_dec(v_val_3180_);
v___x_3182_ = lean_apply_2(v_toPure_3176_, lean_box(0), v_fst_3181_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3183_, lean_object* v_recur_3184_, lean_object* v_it_3185_, lean_object* v_____do__lift_3186_){
_start:
{
if (lean_obj_tag(v_____do__lift_3186_) == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec(v_it_3185_);
lean_dec(v_recur_3184_);
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_apply_2(v_toPure_3183_, lean_box(0), v___x_3187_);
return v___x_3188_;
}
else
{
lean_object* v_val_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3200_; 
v_val_3189_ = lean_ctor_get(v_____do__lift_3186_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_____do__lift_3186_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3191_ = v_____do__lift_3186_;
v_isShared_3192_ = v_isSharedCheck_3200_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_val_3189_);
lean_dec(v_____do__lift_3186_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3200_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
if (lean_obj_tag(v_val_3189_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; 
lean_dec(v_it_3185_);
lean_dec(v_recur_3184_);
v_a_3193_ = lean_ctor_get(v_val_3189_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v_val_3189_, 1);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v_a_3193_);
v___x_3195_ = v___x_3191_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3193_);
v___x_3195_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_apply_2(v_toPure_3183_, lean_box(0), v___x_3195_);
return v___x_3196_;
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
lean_del_object(v___x_3191_);
lean_dec(v_toPure_3183_);
v_a_3198_ = lean_ctor_get(v_val_3189_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v_val_3189_, 1);
v___x_3199_ = lean_apply_4(v_recur_3184_, v_it_3185_, v_a_3198_, lean_box(0), lean_box(0));
return v___x_3199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3201_, lean_object* v___x_3202_, lean_object* v___x_3203_, lean_object* v_____do__lift_3204_){
_start:
{
if (lean_obj_tag(v_____do__lift_3204_) == 0)
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec(v___x_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_apply_2(v_toPure_3201_, lean_box(0), v___x_3205_);
return v___x_3206_;
}
else
{
lean_object* v_val_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3238_; 
v_val_3207_ = lean_ctor_get(v_____do__lift_3204_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_____do__lift_3204_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3209_ = v_____do__lift_3204_;
v_isShared_3210_ = v_isSharedCheck_3238_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_val_3207_);
lean_dec(v_____do__lift_3204_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3238_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
if (lean_obj_tag(v_val_3207_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v___x_3203_);
v_a_3211_ = lean_ctor_get(v_val_3207_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_val_3207_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3213_ = v_val_3207_;
v_isShared_3214_ = v_isSharedCheck_3224_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v_val_3207_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3224_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v_a_3211_);
v___x_3216_ = v___x_3209_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v___x_3202_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3217_);
v___x_3219_ = v___x_3213_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
v___x_3221_ = lean_apply_2(v_toPure_3201_, lean_box(0), v___x_3220_);
return v___x_3221_;
}
}
}
}
else
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3236_; 
v_isSharedCheck_3236_ = !lean_is_exclusive(v_val_3207_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_val_3207_, 0);
lean_dec(v_unused_3237_);
v___x_3226_ = v_val_3207_;
v_isShared_3227_ = v_isSharedCheck_3236_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v_val_3207_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3236_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3203_);
lean_ctor_set(v___x_3228_, 1, v___x_3202_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3228_);
v___x_3230_ = v___x_3226_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3232_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3230_);
v___x_3232_ = v___x_3209_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_apply_2(v_toPure_3201_, lean_box(0), v___x_3232_);
return v___x_3233_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__6(lean_object* v_toPure_3239_, lean_object* v___x_3240_, lean_object* v_inst_3241_, lean_object* v_inst_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_n_u2080_3247_, lean_object* v_filter_3248_, lean_object* v_view_x3f_3249_, lean_object* v_toBind_3250_, lean_object* v___f_3251_, lean_object* v___f_3252_, lean_object* v___f_3253_, lean_object* v___x_3254_, lean_object* v_it_3255_, lean_object* v_acc_3256_, lean_object* v_hP_3257_, lean_object* v_recur_3258_){
_start:
{
lean_object* v_it_3260_; lean_object* v_out_3261_; 
switch(lean_obj_tag(v_it_3255_))
{
case 0:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v_recur_3258_);
lean_dec(v___x_3254_);
lean_dec(v___f_3253_);
lean_dec(v___f_3252_);
lean_dec(v___f_3251_);
lean_dec(v_toBind_3250_);
lean_dec(v_view_x3f_3249_);
lean_dec(v_filter_3248_);
lean_dec(v_n_u2080_3247_);
lean_dec(v_inst_3246_);
lean_dec_ref(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_inst_3243_);
lean_dec_ref(v_inst_3242_);
lean_dec_ref(v_inst_3241_);
lean_dec(v___x_3240_);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_acc_3256_);
v___x_3273_ = lean_apply_2(v_toPure_3239_, lean_box(0), v___x_3272_);
return v___x_3273_;
}
case 1:
{
lean_object* v_pre_3274_; lean_object* v_str_3275_; lean_object* v___x_3276_; 
v_pre_3274_ = lean_ctor_get(v_it_3255_, 0);
lean_inc(v_pre_3274_);
v_str_3275_ = lean_ctor_get(v_it_3255_, 1);
lean_inc_ref(v_str_3275_);
lean_dec_ref_known(v_it_3255_, 2);
v___x_3276_ = l_Lean_Name_str___override(v___x_3254_, v_str_3275_);
v_it_3260_ = v_pre_3274_;
v_out_3261_ = v___x_3276_;
goto v___jp_3259_;
}
default: 
{
lean_object* v_pre_3277_; lean_object* v_i_3278_; lean_object* v___x_3279_; 
v_pre_3277_ = lean_ctor_get(v_it_3255_, 0);
lean_inc(v_pre_3277_);
v_i_3278_ = lean_ctor_get(v_it_3255_, 1);
lean_inc(v_i_3278_);
lean_dec_ref_known(v_it_3255_, 2);
v___x_3279_ = l_Lean_Name_num___override(v___x_3254_, v_i_3278_);
v_it_3260_ = v_pre_3277_;
v_out_3261_ = v___x_3279_;
goto v___jp_3259_;
}
}
v___jp_3259_:
{
lean_object* v_snd_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; lean_object* v___f_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_snd_3262_ = lean_ctor_get(v_acc_3256_, 1);
lean_inc(v_snd_3262_);
lean_dec_ref(v_acc_3256_);
lean_inc(v_toPure_3239_);
v___f_3263_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4), 4, 3);
lean_closure_set(v___f_3263_, 0, v_toPure_3239_);
lean_closure_set(v___f_3263_, 1, v_recur_3258_);
lean_closure_set(v___f_3263_, 2, v_it_3260_);
v___x_3264_ = l_Lean_Name_appendCore(v_out_3261_, v_snd_3262_);
lean_dec(v_out_3261_);
lean_inc(v___x_3264_);
v___f_3265_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5), 4, 3);
lean_closure_set(v___f_3265_, 0, v_toPure_3239_);
lean_closure_set(v___f_3265_, 1, v___x_3264_);
lean_closure_set(v___f_3265_, 2, v___x_3240_);
v___x_3266_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3241_, v_inst_3242_, v_inst_3243_, v_inst_3244_, v_inst_3245_, v_inst_3246_, v_n_u2080_3247_, v_filter_3248_, v_view_x3f_3249_, v___x_3264_);
lean_inc_n(v_toBind_3250_, 4);
v___x_3267_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3266_, v___f_3251_);
v___x_3268_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3267_, v___f_3252_);
v___x_3269_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3268_, v___f_3265_);
v___x_3270_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3269_, v___f_3253_);
v___x_3271_ = lean_apply_4(v_toBind_3250_, lean_box(0), lean_box(0), v___x_3270_, v___f_3263_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_toPure_3280_ = _args[0];
lean_object* v___x_3281_ = _args[1];
lean_object* v_inst_3282_ = _args[2];
lean_object* v_inst_3283_ = _args[3];
lean_object* v_inst_3284_ = _args[4];
lean_object* v_inst_3285_ = _args[5];
lean_object* v_inst_3286_ = _args[6];
lean_object* v_inst_3287_ = _args[7];
lean_object* v_n_u2080_3288_ = _args[8];
lean_object* v_filter_3289_ = _args[9];
lean_object* v_view_x3f_3290_ = _args[10];
lean_object* v_toBind_3291_ = _args[11];
lean_object* v___f_3292_ = _args[12];
lean_object* v___f_3293_ = _args[13];
lean_object* v___f_3294_ = _args[14];
lean_object* v___x_3295_ = _args[15];
lean_object* v_it_3296_ = _args[16];
lean_object* v_acc_3297_ = _args[17];
lean_object* v_hP_3298_ = _args[18];
lean_object* v_recur_3299_ = _args[19];
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__6(v_toPure_3280_, v___x_3281_, v_inst_3282_, v_inst_3283_, v_inst_3284_, v_inst_3285_, v_inst_3286_, v_inst_3287_, v_n_u2080_3288_, v_filter_3289_, v_view_x3f_3290_, v_toBind_3291_, v___f_3292_, v___f_3293_, v___f_3294_, v___x_3295_, v_it_3296_, v_acc_3297_, v_hP_3298_, v_recur_3299_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7(lean_object* v_toPure_3304_, lean_object* v_n_3305_, lean_object* v_inst_3306_, lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_inst_3309_, lean_object* v_inst_3310_, lean_object* v_inst_3311_, lean_object* v_n_u2080_3312_, lean_object* v_filter_3313_, lean_object* v_view_x3f_3314_, lean_object* v_toBind_3315_, lean_object* v___f_3316_, lean_object* v___f_3317_, lean_object* v___f_3318_, lean_object* v_____do__lift_3319_){
_start:
{
if (lean_obj_tag(v_____do__lift_3319_) == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
lean_dec(v___f_3318_);
lean_dec(v___f_3317_);
lean_dec(v___f_3316_);
lean_dec(v_toBind_3315_);
lean_dec(v_view_x3f_3314_);
lean_dec(v_filter_3313_);
lean_dec(v_n_u2080_3312_);
lean_dec(v_inst_3311_);
lean_dec_ref(v_inst_3310_);
lean_dec_ref(v_inst_3309_);
lean_dec_ref(v_inst_3308_);
lean_dec_ref(v_inst_3307_);
lean_dec_ref(v_inst_3306_);
lean_dec(v_n_3305_);
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_apply_2(v_toPure_3304_, lean_box(0), v___x_3320_);
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___f_3326_; lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3322_ = l_Lean_privateToUserName(v_n_3305_);
v___x_3323_ = lean_box(0);
v___x_3324_ = l_Lean_Name_revIter(v___x_3322_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
lean_inc(v_toPure_3304_);
v___f_3326_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3326_, 0, v_toPure_3304_);
lean_closure_set(v___f_3326_, 1, v___x_3325_);
lean_inc(v_toBind_3315_);
v___f_3327_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__6___boxed), 20, 16);
lean_closure_set(v___f_3327_, 0, v_toPure_3304_);
lean_closure_set(v___f_3327_, 1, v___x_3325_);
lean_closure_set(v___f_3327_, 2, v_inst_3306_);
lean_closure_set(v___f_3327_, 3, v_inst_3307_);
lean_closure_set(v___f_3327_, 4, v_inst_3308_);
lean_closure_set(v___f_3327_, 5, v_inst_3309_);
lean_closure_set(v___f_3327_, 6, v_inst_3310_);
lean_closure_set(v___f_3327_, 7, v_inst_3311_);
lean_closure_set(v___f_3327_, 8, v_n_u2080_3312_);
lean_closure_set(v___f_3327_, 9, v_filter_3313_);
lean_closure_set(v___f_3327_, 10, v_view_x3f_3314_);
lean_closure_set(v___f_3327_, 11, v_toBind_3315_);
lean_closure_set(v___f_3327_, 12, v___f_3316_);
lean_closure_set(v___f_3327_, 13, v___f_3317_);
lean_closure_set(v___f_3327_, 14, v___f_3318_);
lean_closure_set(v___f_3327_, 15, v___x_3323_);
v___x_3328_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___closed__0));
v___x_3329_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3327_, v___x_3324_, v___x_3328_, lean_box(0));
v___x_3330_ = lean_apply_4(v_toBind_3315_, lean_box(0), lean_box(0), v___x_3329_, v___f_3326_);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___boxed(lean_object* v_toPure_3331_, lean_object* v_n_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_n_u2080_3339_, lean_object* v_filter_3340_, lean_object* v_view_x3f_3341_, lean_object* v_toBind_3342_, lean_object* v___f_3343_, lean_object* v___f_3344_, lean_object* v___f_3345_, lean_object* v_____do__lift_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7(v_toPure_3331_, v_n_3332_, v_inst_3333_, v_inst_3334_, v_inst_3335_, v_inst_3336_, v_inst_3337_, v_inst_3338_, v_n_u2080_3339_, v_filter_3340_, v_view_x3f_3341_, v_toBind_3342_, v___f_3343_, v___f_3344_, v___f_3345_, v_____do__lift_3346_);
lean_dec(v_____do__lift_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3348_, lean_object* v_inst_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_n_u2080_3354_, lean_object* v_filter_3355_, lean_object* v_view_x3f_3356_, lean_object* v_n_3357_){
_start:
{
lean_object* v___y_3359_; uint8_t v___x_3368_; 
v___x_3368_ = l_Lean_Name_hasMacroScopes(v_n_3357_);
if (v___x_3368_ == 0)
{
lean_object* v_toApplicative_3369_; lean_object* v_toPure_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_toApplicative_3369_ = lean_ctor_get(v_inst_3348_, 0);
v_toPure_3370_ = lean_ctor_get(v_toApplicative_3369_, 1);
v___x_3371_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3370_);
v___x_3372_ = lean_apply_2(v_toPure_3370_, lean_box(0), v___x_3371_);
v___y_3359_ = v___x_3372_;
goto v___jp_3358_;
}
else
{
lean_object* v_toApplicative_3373_; lean_object* v_toPure_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_toApplicative_3373_ = lean_ctor_get(v_inst_3348_, 0);
v_toPure_3374_ = lean_ctor_get(v_toApplicative_3373_, 1);
v___x_3375_ = lean_box(0);
lean_inc(v_toPure_3374_);
v___x_3376_ = lean_apply_2(v_toPure_3374_, lean_box(0), v___x_3375_);
v___y_3359_ = v___x_3376_;
goto v___jp_3358_;
}
v___jp_3358_:
{
lean_object* v_toApplicative_3360_; lean_object* v_toBind_3361_; lean_object* v_toPure_3362_; lean_object* v___f_3363_; lean_object* v___f_3364_; lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; 
v_toApplicative_3360_ = lean_ctor_get(v_inst_3348_, 0);
v_toBind_3361_ = lean_ctor_get(v_inst_3348_, 1);
lean_inc_n(v_toBind_3361_, 2);
v_toPure_3362_ = lean_ctor_get(v_toApplicative_3360_, 1);
lean_inc_n(v_toPure_3362_, 4);
v___f_3363_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3363_, 0, v_toPure_3362_);
v___f_3364_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3364_, 0, v_toPure_3362_);
v___f_3365_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3365_, 0, v_toPure_3362_);
v___f_3366_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__7___boxed), 16, 15);
lean_closure_set(v___f_3366_, 0, v_toPure_3362_);
lean_closure_set(v___f_3366_, 1, v_n_3357_);
lean_closure_set(v___f_3366_, 2, v_inst_3348_);
lean_closure_set(v___f_3366_, 3, v_inst_3349_);
lean_closure_set(v___f_3366_, 4, v_inst_3350_);
lean_closure_set(v___f_3366_, 5, v_inst_3351_);
lean_closure_set(v___f_3366_, 6, v_inst_3352_);
lean_closure_set(v___f_3366_, 7, v_inst_3353_);
lean_closure_set(v___f_3366_, 8, v_n_u2080_3354_);
lean_closure_set(v___f_3366_, 9, v_filter_3355_);
lean_closure_set(v___f_3366_, 10, v_view_x3f_3356_);
lean_closure_set(v___f_3366_, 11, v_toBind_3361_);
lean_closure_set(v___f_3366_, 12, v___f_3365_);
lean_closure_set(v___f_3366_, 13, v___f_3364_);
lean_closure_set(v___f_3366_, 14, v___f_3363_);
v___x_3367_ = lean_apply_4(v_toBind_3361_, lean_box(0), lean_box(0), v___y_3359_, v___f_3366_);
return v___x_3367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3377_, lean_object* v_inst_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_n_u2080_3384_, lean_object* v_filter_3385_, lean_object* v_view_x3f_3386_, lean_object* v_n_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3378_, v_inst_3379_, v_inst_3380_, v_inst_3381_, v_inst_3382_, v_inst_3383_, v_n_u2080_3384_, v_filter_3385_, v_view_x3f_3386_, v_n_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3389_, lean_object* v_x1_3390_, lean_object* v_x2_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = l_Lean_Name_getPrefix(v_x2_3391_);
v___x_3393_ = l_Lean_Name_getPrefix(v_n_u2081_3389_);
v___x_3394_ = l_Lean_Name_isPrefixOf(v___x_3392_, v___x_3393_);
lean_dec(v___x_3393_);
lean_dec(v___x_3392_);
if (v___x_3394_ == 0)
{
lean_dec(v_x2_3391_);
return v_x1_3390_;
}
else
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_array_push(v_x1_3390_, v_x2_3391_);
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3396_, lean_object* v_x1_3397_, lean_object* v_x2_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3396_, v_x1_3397_, v_x2_3398_);
lean_dec(v_n_u2081_3396_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3400_, lean_object* v_n_u2081_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_n_u2080_3408_, lean_object* v_filter_3409_, lean_object* v_toPure_3410_, lean_object* v_____do__lift_3411_){
_start:
{
if (lean_obj_tag(v_____do__lift_3411_) == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v_toPure_3410_);
v___x_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3412_, 0, v_view_3400_);
v___x_3413_ = l_Lean_rootNamespace;
v___x_3414_ = l_Lean_Name_append(v___x_3413_, v_n_u2081_3401_);
v___x_3415_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3402_, v_inst_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_inst_3407_, v_n_u2080_3408_, v_filter_3409_, v___x_3412_, v___x_3414_);
return v___x_3415_;
}
else
{
lean_object* v___x_3416_; 
lean_dec(v_filter_3409_);
lean_dec(v_n_u2080_3408_);
lean_dec(v_inst_3407_);
lean_dec_ref(v_inst_3406_);
lean_dec_ref(v_inst_3405_);
lean_dec_ref(v_inst_3404_);
lean_dec_ref(v_inst_3403_);
lean_dec_ref(v_inst_3402_);
lean_dec(v_n_u2081_3401_);
lean_dec_ref(v_view_3400_);
v___x_3416_ = lean_apply_2(v_toPure_3410_, lean_box(0), v_____do__lift_3411_);
return v___x_3416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_n_u2080_3424_, lean_object* v_filter_3425_, lean_object* v___x_3426_, lean_object* v_toBind_3427_, lean_object* v___f_3428_, uint8_t v_allowHorizAliases_3429_, lean_object* v___f_3430_, lean_object* v_____do__lift_3431_){
_start:
{
lean_object* v_aliases_3433_; 
if (lean_obj_tag(v_____do__lift_3431_) == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_dec_ref(v___f_3430_);
lean_dec(v___f_3428_);
lean_dec(v_toBind_3427_);
lean_dec_ref(v___x_3426_);
lean_dec(v_filter_3425_);
lean_dec(v_n_u2080_3424_);
lean_dec(v_inst_3423_);
lean_dec_ref(v_inst_3422_);
lean_dec_ref(v_inst_3421_);
lean_dec_ref(v_inst_3420_);
lean_dec_ref(v_inst_3419_);
lean_dec_ref(v_inst_3418_);
v___x_3439_ = lean_box(0);
v___x_3440_ = lean_apply_2(v_toPure_3417_, lean_box(0), v___x_3439_);
return v___x_3440_;
}
else
{
lean_object* v_val_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec(v_toPure_3417_);
v_val_3441_ = lean_ctor_get(v_____do__lift_3431_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v_____do__lift_3431_, 1);
lean_inc(v_n_u2080_3424_);
v___x_3442_ = l_Lean_getRevAliases(v_val_3441_, v_n_u2080_3424_);
v___x_3443_ = lean_array_mk(v___x_3442_);
if (v_allowHorizAliases_3429_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = lean_array_get_size(v___x_3443_);
v___x_3446_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3447_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3448_ = lean_nat_dec_lt(v___x_3444_, v___x_3445_);
if (v___x_3448_ == 0)
{
lean_dec_ref(v___x_3443_);
lean_dec_ref(v___f_3430_);
v_aliases_3433_ = v___x_3446_;
goto v___jp_3432_;
}
else
{
size_t v___x_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = ((size_t)0ULL);
v___x_3450_ = lean_usize_of_nat(v___x_3445_);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3447_, v___f_3430_, v___x_3443_, v___x_3449_, v___x_3450_, v___x_3446_);
v_aliases_3433_ = v___x_3451_;
goto v___jp_3432_;
}
}
else
{
lean_dec_ref(v___f_3430_);
v_aliases_3433_ = v___x_3443_;
goto v___jp_3432_;
}
}
v___jp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3435_, 0, lean_box(0));
lean_closure_set(v___x_3435_, 1, v_inst_3418_);
lean_closure_set(v___x_3435_, 2, v_inst_3419_);
lean_closure_set(v___x_3435_, 3, v_inst_3420_);
lean_closure_set(v___x_3435_, 4, v_inst_3421_);
lean_closure_set(v___x_3435_, 5, v_inst_3422_);
lean_closure_set(v___x_3435_, 6, v_inst_3423_);
lean_closure_set(v___x_3435_, 7, v_n_u2080_3424_);
lean_closure_set(v___x_3435_, 8, v_filter_3425_);
lean_closure_set(v___x_3435_, 9, v___x_3434_);
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3426_, v___x_3435_, v_aliases_3433_, v___x_3436_);
v___x_3438_ = lean_apply_4(v_toBind_3427_, lean_box(0), lean_box(0), v___x_3437_, v___f_3428_);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_inst_3455_, lean_object* v_inst_3456_, lean_object* v_inst_3457_, lean_object* v_inst_3458_, lean_object* v_n_u2080_3459_, lean_object* v_filter_3460_, lean_object* v___x_3461_, lean_object* v_toBind_3462_, lean_object* v___f_3463_, lean_object* v_allowHorizAliases_3464_, lean_object* v___f_3465_, lean_object* v_____do__lift_3466_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3467_; lean_object* v_res_3468_; 
v_allowHorizAliases_boxed_3467_ = lean_unbox(v_allowHorizAliases_3464_);
v_res_3468_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3452_, v_inst_3453_, v_inst_3454_, v_inst_3455_, v_inst_3456_, v_inst_3457_, v_inst_3458_, v_n_u2080_3459_, v_filter_3460_, v___x_3461_, v_toBind_3462_, v___f_3463_, v_allowHorizAliases_boxed_3467_, v___f_3465_, v_____do__lift_3466_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3469_, lean_object* v_____do__lift_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_____do__lift_3470_);
v___x_3472_ = lean_apply_2(v_toPure_3469_, lean_box(0), v___x_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_n_u2080_3480_, lean_object* v_filter_3481_, lean_object* v___x_3482_, lean_object* v_toPure_3483_, lean_object* v_____do__lift_3484_){
_start:
{
if (lean_obj_tag(v_____do__lift_3484_) == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_toPure_3483_);
v___x_3485_ = l_Lean_rootNamespace;
v___x_3486_ = l_Lean_Name_append(v___x_3485_, v_n_u2081_3473_);
v___x_3487_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3474_, v_inst_3475_, v_inst_3476_, v_inst_3477_, v_inst_3478_, v_inst_3479_, v_n_u2080_3480_, v_filter_3481_, v___x_3482_, v___x_3486_);
return v___x_3487_;
}
else
{
lean_object* v___x_3488_; 
lean_dec(v___x_3482_);
lean_dec(v_filter_3481_);
lean_dec(v_n_u2080_3480_);
lean_dec(v_inst_3479_);
lean_dec_ref(v_inst_3478_);
lean_dec_ref(v_inst_3477_);
lean_dec_ref(v_inst_3476_);
lean_dec_ref(v_inst_3475_);
lean_dec_ref(v_inst_3474_);
lean_dec(v_n_u2081_3473_);
v___x_3488_ = lean_apply_2(v_toPure_3483_, lean_box(0), v_____do__lift_3484_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_n_u2080_3495_, uint8_t v_fullNames_3496_, uint8_t v_allowHorizAliases_3497_, lean_object* v_filter_3498_){
_start:
{
lean_object* v_view_3499_; lean_object* v_name_3500_; lean_object* v_n_u2081_3501_; lean_object* v___x_3502_; 
lean_inc(v_n_u2080_3495_);
v_view_3499_ = l_Lean_extractMacroScopes(v_n_u2080_3495_);
v_name_3500_ = lean_ctor_get(v_view_3499_, 0);
lean_inc(v_name_3500_);
v_n_u2081_3501_ = l_Lean_privateToUserName(v_name_3500_);
lean_inc_ref(v_inst_3489_);
v___x_3502_ = l_OptionT_instAlternative___redArg(v_inst_3489_);
if (v_fullNames_3496_ == 0)
{
lean_object* v_toApplicative_3503_; lean_object* v_getEnv_3504_; lean_object* v_toBind_3505_; lean_object* v_toPure_3506_; lean_object* v___f_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v___f_3510_; lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_toApplicative_3503_ = lean_ctor_get(v_inst_3489_, 0);
v_getEnv_3504_ = lean_ctor_get(v_inst_3491_, 0);
lean_inc(v_getEnv_3504_);
v_toBind_3505_ = lean_ctor_get(v_inst_3489_, 1);
lean_inc_n(v_toBind_3505_, 3);
v_toPure_3506_ = lean_ctor_get(v_toApplicative_3503_, 1);
lean_inc_n(v_toPure_3506_, 3);
lean_inc(v_n_u2081_3501_);
v___f_3507_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3507_, 0, v_n_u2081_3501_);
lean_inc(v_filter_3498_);
lean_inc(v_n_u2080_3495_);
lean_inc(v_inst_3494_);
lean_inc_ref(v_inst_3493_);
lean_inc_ref(v_inst_3492_);
lean_inc_ref(v_inst_3491_);
lean_inc_ref(v_inst_3490_);
lean_inc_ref(v_inst_3489_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3508_, 0, v_view_3499_);
lean_closure_set(v___f_3508_, 1, v_n_u2081_3501_);
lean_closure_set(v___f_3508_, 2, v_inst_3489_);
lean_closure_set(v___f_3508_, 3, v_inst_3490_);
lean_closure_set(v___f_3508_, 4, v_inst_3491_);
lean_closure_set(v___f_3508_, 5, v_inst_3492_);
lean_closure_set(v___f_3508_, 6, v_inst_3493_);
lean_closure_set(v___f_3508_, 7, v_inst_3494_);
lean_closure_set(v___f_3508_, 8, v_n_u2080_3495_);
lean_closure_set(v___f_3508_, 9, v_filter_3498_);
lean_closure_set(v___f_3508_, 10, v_toPure_3506_);
v___x_3509_ = lean_box(v_allowHorizAliases_3497_);
v___f_3510_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_3510_, 0, v_toPure_3506_);
lean_closure_set(v___f_3510_, 1, v_inst_3489_);
lean_closure_set(v___f_3510_, 2, v_inst_3490_);
lean_closure_set(v___f_3510_, 3, v_inst_3491_);
lean_closure_set(v___f_3510_, 4, v_inst_3492_);
lean_closure_set(v___f_3510_, 5, v_inst_3493_);
lean_closure_set(v___f_3510_, 6, v_inst_3494_);
lean_closure_set(v___f_3510_, 7, v_n_u2080_3495_);
lean_closure_set(v___f_3510_, 8, v_filter_3498_);
lean_closure_set(v___f_3510_, 9, v___x_3502_);
lean_closure_set(v___f_3510_, 10, v_toBind_3505_);
lean_closure_set(v___f_3510_, 11, v___f_3508_);
lean_closure_set(v___f_3510_, 12, v___x_3509_);
lean_closure_set(v___f_3510_, 13, v___f_3507_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3511_, 0, v_toPure_3506_);
v___x_3512_ = lean_apply_4(v_toBind_3505_, lean_box(0), lean_box(0), v_getEnv_3504_, v___f_3511_);
v___x_3513_ = lean_apply_4(v_toBind_3505_, lean_box(0), lean_box(0), v___x_3512_, v___f_3510_);
return v___x_3513_;
}
else
{
lean_object* v_toApplicative_3514_; lean_object* v_toBind_3515_; lean_object* v_toPure_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; 
lean_dec_ref(v___x_3502_);
v_toApplicative_3514_ = lean_ctor_get(v_inst_3489_, 0);
v_toBind_3515_ = lean_ctor_get(v_inst_3489_, 1);
lean_inc(v_toBind_3515_);
v_toPure_3516_ = lean_ctor_get(v_toApplicative_3514_, 1);
lean_inc(v_toPure_3516_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_view_3499_);
lean_inc(v_n_u2081_3501_);
lean_inc_ref(v___x_3517_);
lean_inc(v_filter_3498_);
lean_inc(v_n_u2080_3495_);
lean_inc(v_inst_3494_);
lean_inc_ref(v_inst_3493_);
lean_inc_ref(v_inst_3492_);
lean_inc_ref(v_inst_3491_);
lean_inc_ref(v_inst_3490_);
lean_inc_ref(v_inst_3489_);
v___x_3518_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3489_, v_inst_3490_, v_inst_3491_, v_inst_3492_, v_inst_3493_, v_inst_3494_, v_n_u2080_3495_, v_filter_3498_, v___x_3517_, v_n_u2081_3501_);
v___f_3519_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3519_, 0, v_n_u2081_3501_);
lean_closure_set(v___f_3519_, 1, v_inst_3489_);
lean_closure_set(v___f_3519_, 2, v_inst_3490_);
lean_closure_set(v___f_3519_, 3, v_inst_3491_);
lean_closure_set(v___f_3519_, 4, v_inst_3492_);
lean_closure_set(v___f_3519_, 5, v_inst_3493_);
lean_closure_set(v___f_3519_, 6, v_inst_3494_);
lean_closure_set(v___f_3519_, 7, v_n_u2080_3495_);
lean_closure_set(v___f_3519_, 8, v_filter_3498_);
lean_closure_set(v___f_3519_, 9, v___x_3517_);
lean_closure_set(v___f_3519_, 10, v_toPure_3516_);
v___x_3520_ = lean_apply_4(v_toBind_3515_, lean_box(0), lean_box(0), v___x_3518_, v___f_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_n_u2080_3527_, lean_object* v_fullNames_3528_, lean_object* v_allowHorizAliases_3529_, lean_object* v_filter_3530_){
_start:
{
uint8_t v_fullNames_boxed_3531_; uint8_t v_allowHorizAliases_boxed_3532_; lean_object* v_res_3533_; 
v_fullNames_boxed_3531_ = lean_unbox(v_fullNames_3528_);
v_allowHorizAliases_boxed_3532_ = lean_unbox(v_allowHorizAliases_3529_);
v_res_3533_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3521_, v_inst_3522_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v_inst_3526_, v_n_u2080_3527_, v_fullNames_boxed_3531_, v_allowHorizAliases_boxed_3532_, v_filter_3530_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_n_u2080_3541_, uint8_t v_fullNames_3542_, uint8_t v_allowHorizAliases_3543_, lean_object* v_filter_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3535_, v_inst_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_inst_3540_, v_n_u2080_3541_, v_fullNames_3542_, v_allowHorizAliases_3543_, v_filter_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3546_, lean_object* v_inst_3547_, lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_n_u2080_3553_, lean_object* v_fullNames_3554_, lean_object* v_allowHorizAliases_3555_, lean_object* v_filter_3556_){
_start:
{
uint8_t v_fullNames_boxed_3557_; uint8_t v_allowHorizAliases_boxed_3558_; lean_object* v_res_3559_; 
v_fullNames_boxed_3557_ = lean_unbox(v_fullNames_3554_);
v_allowHorizAliases_boxed_3558_ = lean_unbox(v_allowHorizAliases_3555_);
v_res_3559_ = l_Lean_unresolveNameGlobal_x3f(v_m_3546_, v_inst_3547_, v_inst_3548_, v_inst_3549_, v_inst_3550_, v_inst_3551_, v_inst_3552_, v_n_u2080_3553_, v_fullNames_boxed_3557_, v_allowHorizAliases_boxed_3558_, v_filter_3556_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3560_, lean_object* v_n_u2080_3561_, lean_object* v_n_x3f_3562_){
_start:
{
if (lean_obj_tag(v_n_x3f_3562_) == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_apply_2(v_toPure_3560_, lean_box(0), v_n_u2080_3561_);
return v___x_3563_;
}
else
{
lean_object* v_val_3564_; lean_object* v___x_3565_; 
lean_dec(v_n_u2080_3561_);
v_val_3564_ = lean_ctor_get(v_n_x3f_3562_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v_n_x3f_3562_, 1);
v___x_3565_ = lean_apply_2(v_toPure_3560_, lean_box(0), v_val_3564_);
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_n_u2080_3572_, uint8_t v_fullNames_3573_, uint8_t v_allowHorizAliases_3574_, lean_object* v_filter_3575_){
_start:
{
lean_object* v_toApplicative_3576_; lean_object* v_toBind_3577_; lean_object* v_toPure_3578_; lean_object* v___x_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; 
v_toApplicative_3576_ = lean_ctor_get(v_inst_3566_, 0);
v_toBind_3577_ = lean_ctor_get(v_inst_3566_, 1);
lean_inc(v_toBind_3577_);
v_toPure_3578_ = lean_ctor_get(v_toApplicative_3576_, 1);
lean_inc(v_toPure_3578_);
lean_inc(v_n_u2080_3572_);
v___x_3579_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3566_, v_inst_3567_, v_inst_3568_, v_inst_3569_, v_inst_3570_, v_inst_3571_, v_n_u2080_3572_, v_fullNames_3573_, v_allowHorizAliases_3574_, v_filter_3575_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3580_, 0, v_toPure_3578_);
lean_closure_set(v___f_3580_, 1, v_n_u2080_3572_);
v___x_3581_ = lean_apply_4(v_toBind_3577_, lean_box(0), lean_box(0), v___x_3579_, v___f_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_n_u2080_3588_, lean_object* v_fullNames_3589_, lean_object* v_allowHorizAliases_3590_, lean_object* v_filter_3591_){
_start:
{
uint8_t v_fullNames_boxed_3592_; uint8_t v_allowHorizAliases_boxed_3593_; lean_object* v_res_3594_; 
v_fullNames_boxed_3592_ = lean_unbox(v_fullNames_3589_);
v_allowHorizAliases_boxed_3593_ = lean_unbox(v_allowHorizAliases_3590_);
v_res_3594_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3582_, v_inst_3583_, v_inst_3584_, v_inst_3585_, v_inst_3586_, v_inst_3587_, v_n_u2080_3588_, v_fullNames_boxed_3592_, v_allowHorizAliases_boxed_3593_, v_filter_3591_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_n_u2080_3602_, uint8_t v_fullNames_3603_, uint8_t v_allowHorizAliases_3604_, lean_object* v_filter_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_n_u2080_3602_, v_fullNames_3603_, v_allowHorizAliases_3604_, v_filter_3605_);
return v___x_3606_;
}
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_n_u2080_3642_, uint8_t v_fullNames_3643_){
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_inst_3651_, lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_inst_3654_, lean_object* v_inst_3655_, lean_object* v_n_u2080_3656_, lean_object* v_fullNames_3657_){
_start:
{
uint8_t v_fullNames_boxed_3658_; lean_object* v_res_3659_; 
v_fullNames_boxed_3658_ = lean_unbox(v_fullNames_3657_);
v_res_3659_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3649_, v_inst_3650_, v_inst_3651_, v_inst_3652_, v_inst_3653_, v_inst_3654_, v_inst_3655_, v_n_u2080_3656_, v_fullNames_boxed_3658_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_inst_3666_, lean_object* v_inst_3667_, lean_object* v_n_u2080_3668_, uint8_t v_fullNames_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3661_, v_inst_3662_, v_inst_3663_, v_inst_3664_, v_inst_3665_, v_inst_3666_, v_inst_3667_, v_n_u2080_3668_, v_fullNames_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3671_, lean_object* v_inst_3672_, lean_object* v_inst_3673_, lean_object* v_inst_3674_, lean_object* v_inst_3675_, lean_object* v_inst_3676_, lean_object* v_inst_3677_, lean_object* v_inst_3678_, lean_object* v_n_u2080_3679_, lean_object* v_fullNames_3680_){
_start:
{
uint8_t v_fullNames_boxed_3681_; lean_object* v_res_3682_; 
v_fullNames_boxed_3681_ = lean_unbox(v_fullNames_3680_);
v_res_3682_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3671_, v_inst_3672_, v_inst_3673_, v_inst_3674_, v_inst_3675_, v_inst_3676_, v_inst_3677_, v_inst_3678_, v_n_u2080_3679_, v_fullNames_boxed_3681_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_inst_3687_, lean_object* v_inst_3688_, lean_object* v_inst_3689_, lean_object* v_n_u2080_3690_, uint8_t v_fullNames_3691_){
_start:
{
lean_object* v_toApplicative_3692_; lean_object* v_toBind_3693_; lean_object* v_toPure_3694_; lean_object* v___x_3695_; lean_object* v___f_3696_; lean_object* v___x_3697_; 
v_toApplicative_3692_ = lean_ctor_get(v_inst_3683_, 0);
v_toBind_3693_ = lean_ctor_get(v_inst_3683_, 1);
lean_inc(v_toBind_3693_);
v_toPure_3694_ = lean_ctor_get(v_toApplicative_3692_, 1);
lean_inc(v_toPure_3694_);
lean_inc(v_n_u2080_3690_);
v___x_3695_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3683_, v_inst_3684_, v_inst_3685_, v_inst_3686_, v_inst_3687_, v_inst_3688_, v_inst_3689_, v_n_u2080_3690_, v_fullNames_3691_);
v___f_3696_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3696_, 0, v_toPure_3694_);
lean_closure_set(v___f_3696_, 1, v_n_u2080_3690_);
v___x_3697_ = lean_apply_4(v_toBind_3693_, lean_box(0), lean_box(0), v___x_3695_, v___f_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3698_, lean_object* v_inst_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_n_u2080_3705_, lean_object* v_fullNames_3706_){
_start:
{
uint8_t v_fullNames_boxed_3707_; lean_object* v_res_3708_; 
v_fullNames_boxed_3707_ = lean_unbox(v_fullNames_3706_);
v_res_3708_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3698_, v_inst_3699_, v_inst_3700_, v_inst_3701_, v_inst_3702_, v_inst_3703_, v_inst_3704_, v_n_u2080_3705_, v_fullNames_boxed_3707_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3709_, lean_object* v_inst_3710_, lean_object* v_inst_3711_, lean_object* v_inst_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_n_u2080_3717_, uint8_t v_fullNames_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3710_, v_inst_3711_, v_inst_3712_, v_inst_3713_, v_inst_3714_, v_inst_3715_, v_inst_3716_, v_n_u2080_3717_, v_fullNames_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3720_, lean_object* v_inst_3721_, lean_object* v_inst_3722_, lean_object* v_inst_3723_, lean_object* v_inst_3724_, lean_object* v_inst_3725_, lean_object* v_inst_3726_, lean_object* v_inst_3727_, lean_object* v_n_u2080_3728_, lean_object* v_fullNames_3729_){
_start:
{
uint8_t v_fullNames_boxed_3730_; lean_object* v_res_3731_; 
v_fullNames_boxed_3730_ = lean_unbox(v_fullNames_3729_);
v_res_3731_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3720_, v_inst_3721_, v_inst_3722_, v_inst_3723_, v_inst_3724_, v_inst_3725_, v_inst_3726_, v_inst_3727_, v_n_u2080_3728_, v_fullNames_boxed_3730_);
return v_res_3731_;
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
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_3911018964____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ResolveName_0__Lean_reservedNamePredsRef);
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
