// Lean compiler output
// Module: Lean.Widget.UserWidget
// Imports: public import Lean.Elab.Eval public import Lean.Server.Rpc.RequestHandling
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
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_UInt64_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_bignumToJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_instToExprName___private__1(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Widget"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__2 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__2_value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(222, 167, 125, 136, 228, 207, 28, 37)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "WidgetInstance"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__0_value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 26, 248, 187, 7, 143, 98, 88)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instToModuleModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Widget_instToModuleModule___closed__0 = (const lean_object*)&l_Lean_Widget_instToModuleModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToModuleModule = (const lean_object*)&l_Lean_Widget_instToModuleModule___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addBuiltinModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 115, 46, 200, 151, 151, 185, 65)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UserWidget"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 103, 214, 126, 13, 168, 26, 227)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(92, 251, 38, 1, 61, 247, 222, 51)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 50, 155, 99, 229, 150, 16, 192)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 81, 65, 205, 201, 62, 183, 195)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moduleRegistry"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 46, 162, 28, 144, 98, 40, 33)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "addBuiltinModule"};
static const lean_object* l_Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "A widget module with the same hash(JS source code) was already registered at "};
static const lean_object* l_Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToModule"};
static const lean_object* l_Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toModule"};
static const lean_object* l_Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "A builtin widget module with the same hash(JS source code) was already registered."};
static const lean_object* l_Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_array_object l_Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "widgetModuleAttrImpl"};
static const lean_object* l_Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 203, 59, 214, 15, 221, 203, 217)}};
static const lean_object* l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "Registers a widget module. Its type must implement Lean.Widget.ToModule."};
static const lean_object* l_Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l_Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_widget_module"};
static const lean_object* l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 42, 123, 194, 197, 140, 191, 110)}};
static const lean_object* l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "widget_module"};
static const lean_object* l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 72, 138, 198, 227, 75, 129, 42)}};
static const lean_object* l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_widgetModuleAttrImpl;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hash"};
static const lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0_value;
static const lean_string_object l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1 = (const lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1_value;
static const lean_array_object l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2 = (const lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonGetWidgetSourceParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams = (const lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "GetWidgetSourceParams"};
static const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 36, 203, 156, 237, 33, 76, 231)}};
static const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3;
static const lean_ctor_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 103, 194, 67, 121, 216, 187, 106)}};
static const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6;
static const lean_string_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8;
static const lean_ctor_object l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonGetWidgetSourceParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams = (const lean_object*)&l_Lean_Widget_instFromJsonGetWidgetSourceParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedWidgetSource_default = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedWidgetSource = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
static const lean_string_object l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sourcetext"};
static const lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonWidgetSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonWidgetSource_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonWidgetSource___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonWidgetSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonWidgetSource = (const lean_object*)&l_Lean_Widget_instToJsonWidgetSource___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "WidgetSource"};
static const lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 228, 124, 26, 26, 173, 31, 40)}};
static const lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2;
static lean_once_cell_t l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3;
static const lean_ctor_object l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 49, 211, 208, 134, 118, 118, 141)}};
static const lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4 = (const lean_object*)&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5;
static lean_once_cell_t l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6;
static lean_once_cell_t l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonWidgetSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonWidgetSource_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonWidgetSource___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonWidgetSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonWidgetSource = (const lean_object*)&l_Lean_Widget_instFromJsonWidgetSource___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_getWidgetSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "No widget module with hash "};
static const lean_object* l_Lean_Widget_getWidgetSource___closed__0 = (const lean_object*)&l_Lean_Widget_getWidgetSource___closed__0_value;
static const lean_string_object l_Lean_Widget_getWidgetSource___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " registered"};
static const lean_object* l_Lean_Widget_getWidgetSource___closed__1 = (const lean_object*)&l_Lean_Widget_getWidgetSource___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Cannot decode params in RPC call '"};
static const lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0_value;
static const lean_string_object l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1_value;
static const lean_string_object l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ")'\n"};
static const lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2_value;
static const lean_string_object l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Outdated RPC session"};
static const lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__3 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(9, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Failed to register builtin RPC call handler for '"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = ": only possible during initialization"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2_value;
static const lean_string_object l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ": already registered"};
static const lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3 = (const lean_object*)&l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "getWidgetSource"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 105, 173, 159, 3, 254, 1, 84)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_getWidgetSource___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "panelWidgetsExt"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(45, 5, 183, 119, 198, 138, 143, 105)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_evalPanelWidgets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_evalPanelWidgets___closed__0 = (const lean_object*)&l_Lean_Widget_evalPanelWidgets___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget(lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedUserWidgetDefinition_default;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedUserWidgetDefinition;
static const lean_string_object l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0_value;
static const lean_string_object l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "javascript"};
static const lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1 = (const lean_object*)&l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonUserWidgetDefinition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonUserWidgetDefinition_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonUserWidgetDefinition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition = (const lean_object*)&l_Lean_Widget_instToJsonUserWidgetDefinition___closed__0_value;
static const lean_string_object l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "UserWidgetDefinition"};
static const lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 148, 125, 199, 96, 60, 76, 213)}};
static const lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3;
static const lean_ctor_object l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4 = (const lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7;
static const lean_ctor_object l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 118, 184, 62, 15, 192, 226, 192)}};
static const lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8 = (const lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10;
static lean_once_cell_t l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonUserWidgetDefinition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition = (const lean_object*)&l_Lean_Widget_instFromJsonUserWidgetDefinition___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToModuleUserWidgetDefinition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___closed__0 = (const lean_object*)&l_Lean_Widget_instToModuleUserWidgetDefinition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition = (const lean_object*)&l_Lean_Widget_instToModuleUserWidgetDefinition___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_stringToMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0 = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "javascriptHash"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "props"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__0 = (const lean_object*)&l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__0_value;
static const lean_closure_object l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__1 = (const lean_object*)&l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__0_value),((lean_object*)&l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__1_value)}};
static const lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__2 = (const lean_object*)&l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance = (const lean_object*)&l_Lean_Widget_instRpcEncodablePanelWidgetInstance___closed__2_value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "widgets"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28__value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__0 = (const lean_object*)&l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__0_value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__1 = (const lean_object*)&l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__0_value),((lean_object*)&l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__1_value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__2 = (const lean_object*)&l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse = (const lean_object*)&l_Lean_Widget_instRpcEncodableGetWidgetsResponse___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_getWidgets___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_getWidgets___lam__1___closed__0 = (const lean_object*)&l_Lean_Widget_getWidgets___lam__1___closed__0_value;
static const lean_array_object l_Lean_Widget_getWidgets___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_getWidgets___lam__1___closed__1 = (const lean_object*)&l_Lean_Widget_getWidgets___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "getWidgets"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 94, 165, 187, 253, 193, 202, 121)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_getWidgets___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__3));
v___x_15_ = 1;
v___x_16_ = 1;
v___x_17_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_14_, v_e_8_, v___x_15_, v___x_16_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___boxed(lean_object* v_e_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_e_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(lean_object* v_e_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; lean_object* v___x_39_; 
v___x_36_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1));
v___x_37_ = 1;
v___x_38_ = 1;
v___x_39_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_36_, v_e_30_, v___x_37_, v___x_38_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___boxed(lean_object* v_e_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_e_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(1);
v___x_51_ = lean_st_mk_ref(v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(uint64_t v_k_55_, lean_object* v_v_56_, lean_object* v_t_57_){
_start:
{
if (lean_obj_tag(v_t_57_) == 0)
{
lean_object* v_size_58_; lean_object* v_k_59_; lean_object* v_v_60_; lean_object* v_l_61_; lean_object* v_r_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_346_; 
v_size_58_ = lean_ctor_get(v_t_57_, 0);
v_k_59_ = lean_ctor_get(v_t_57_, 1);
v_v_60_ = lean_ctor_get(v_t_57_, 2);
v_l_61_ = lean_ctor_get(v_t_57_, 3);
v_r_62_ = lean_ctor_get(v_t_57_, 4);
v_isSharedCheck_346_ = !lean_is_exclusive(v_t_57_);
if (v_isSharedCheck_346_ == 0)
{
v___x_64_ = v_t_57_;
v_isShared_65_ = v_isSharedCheck_346_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_r_62_);
lean_inc(v_l_61_);
lean_inc(v_v_60_);
lean_inc(v_k_59_);
lean_inc(v_size_58_);
lean_dec(v_t_57_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_346_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
uint64_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unbox_uint64(v_k_59_);
v___x_67_ = lean_uint64_dec_lt(v_k_55_, v___x_66_);
if (v___x_67_ == 0)
{
uint64_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_unbox_uint64(v_k_59_);
v___x_69_ = lean_uint64_dec_eq(v_k_55_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v_impl_70_; lean_object* v___x_71_; 
lean_dec(v_size_58_);
v_impl_70_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_55_, v_v_56_, v_r_62_);
v___x_71_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_61_) == 0)
{
lean_object* v_size_72_; lean_object* v_size_73_; lean_object* v_k_74_; lean_object* v_v_75_; lean_object* v_l_76_; lean_object* v_r_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_size_72_ = lean_ctor_get(v_l_61_, 0);
v_size_73_ = lean_ctor_get(v_impl_70_, 0);
lean_inc(v_size_73_);
v_k_74_ = lean_ctor_get(v_impl_70_, 1);
lean_inc(v_k_74_);
v_v_75_ = lean_ctor_get(v_impl_70_, 2);
lean_inc(v_v_75_);
v_l_76_ = lean_ctor_get(v_impl_70_, 3);
lean_inc(v_l_76_);
v_r_77_ = lean_ctor_get(v_impl_70_, 4);
lean_inc(v_r_77_);
v___x_78_ = lean_unsigned_to_nat(3u);
v___x_79_ = lean_nat_mul(v___x_78_, v_size_72_);
v___x_80_ = lean_nat_dec_lt(v___x_79_, v_size_73_);
lean_dec(v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_r_77_);
lean_dec(v_l_76_);
lean_dec(v_v_75_);
lean_dec(v_k_74_);
v___x_81_ = lean_nat_add(v___x_71_, v_size_72_);
v___x_82_ = lean_nat_add(v___x_81_, v_size_73_);
lean_dec(v_size_73_);
lean_dec(v___x_81_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_impl_70_);
lean_ctor_set(v___x_64_, 0, v___x_82_);
v___x_84_ = v___x_64_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v_l_61_);
lean_ctor_set(v_reuseFailAlloc_85_, 4, v_impl_70_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_149_; 
v_isSharedCheck_149_ = !lean_is_exclusive(v_impl_70_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; 
v_unused_150_ = lean_ctor_get(v_impl_70_, 4);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v_impl_70_, 3);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_impl_70_, 2);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_impl_70_, 1);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_impl_70_, 0);
lean_dec(v_unused_154_);
v___x_87_ = v_impl_70_;
v_isShared_88_ = v_isSharedCheck_149_;
goto v_resetjp_86_;
}
else
{
lean_dec(v_impl_70_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_149_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_size_89_; lean_object* v_k_90_; lean_object* v_v_91_; lean_object* v_l_92_; lean_object* v_r_93_; lean_object* v_size_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_size_89_ = lean_ctor_get(v_l_76_, 0);
v_k_90_ = lean_ctor_get(v_l_76_, 1);
v_v_91_ = lean_ctor_get(v_l_76_, 2);
v_l_92_ = lean_ctor_get(v_l_76_, 3);
v_r_93_ = lean_ctor_get(v_l_76_, 4);
v_size_94_ = lean_ctor_get(v_r_77_, 0);
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = lean_nat_mul(v___x_95_, v_size_94_);
v___x_97_ = lean_nat_dec_lt(v_size_89_, v___x_96_);
lean_dec(v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_125_; 
lean_inc(v_r_93_);
lean_inc(v_l_92_);
lean_inc(v_v_91_);
lean_inc(v_k_90_);
v_isSharedCheck_125_ = !lean_is_exclusive(v_l_76_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; lean_object* v_unused_127_; lean_object* v_unused_128_; lean_object* v_unused_129_; lean_object* v_unused_130_; 
v_unused_126_ = lean_ctor_get(v_l_76_, 4);
lean_dec(v_unused_126_);
v_unused_127_ = lean_ctor_get(v_l_76_, 3);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_l_76_, 2);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_l_76_, 1);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_l_76_, 0);
lean_dec(v_unused_130_);
v___x_99_ = v_l_76_;
v_isShared_100_ = v_isSharedCheck_125_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_l_76_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_125_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_115_; 
v___x_101_ = lean_nat_add(v___x_71_, v_size_72_);
v___x_102_ = lean_nat_add(v___x_101_, v_size_73_);
lean_dec(v_size_73_);
if (lean_obj_tag(v_l_92_) == 0)
{
lean_object* v_size_123_; 
v_size_123_ = lean_ctor_get(v_l_92_, 0);
lean_inc(v_size_123_);
v___y_115_ = v_size_123_;
goto v___jp_114_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___y_115_ = v___x_124_;
goto v___jp_114_;
}
v___jp_103_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_nat_add(v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 4, v_r_77_);
lean_ctor_set(v___x_99_, 3, v_r_93_);
lean_ctor_set(v___x_99_, 2, v_v_75_);
lean_ctor_set(v___x_99_, 1, v_k_74_);
lean_ctor_set(v___x_99_, 0, v___x_107_);
v___x_109_ = v___x_99_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_74_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_75_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_r_93_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_r_77_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v___x_109_);
lean_ctor_set(v___x_87_, 3, v___y_104_);
lean_ctor_set(v___x_87_, 2, v_v_91_);
lean_ctor_set(v___x_87_, 1, v_k_90_);
lean_ctor_set(v___x_87_, 0, v___x_102_);
v___x_111_ = v___x_87_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_k_90_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_v_91_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v___y_104_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_nat_add(v___x_101_, v___y_115_);
lean_dec(v___y_115_);
lean_dec(v___x_101_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_l_92_);
lean_ctor_set(v___x_64_, 0, v___x_116_);
v___x_118_ = v___x_64_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v_l_61_);
lean_ctor_set(v_reuseFailAlloc_122_, 4, v_l_92_);
v___x_118_ = v_reuseFailAlloc_122_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_nat_add(v___x_71_, v_size_94_);
if (lean_obj_tag(v_r_93_) == 0)
{
lean_object* v_size_120_; 
v_size_120_ = lean_ctor_get(v_r_93_, 0);
lean_inc(v_size_120_);
v___y_104_ = v___x_118_;
v___y_105_ = v___x_119_;
v___y_106_ = v_size_120_;
goto v___jp_103_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___y_104_ = v___x_118_;
v___y_105_ = v___x_119_;
v___y_106_ = v___x_121_;
goto v___jp_103_;
}
}
}
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
lean_del_object(v___x_64_);
v___x_131_ = lean_nat_add(v___x_71_, v_size_72_);
v___x_132_ = lean_nat_add(v___x_131_, v_size_73_);
lean_dec(v_size_73_);
v___x_133_ = lean_nat_add(v___x_131_, v_size_89_);
lean_dec(v___x_131_);
lean_inc_ref(v_l_61_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_l_76_);
lean_ctor_set(v___x_87_, 3, v_l_61_);
lean_ctor_set(v___x_87_, 2, v_v_60_);
lean_ctor_set(v___x_87_, 1, v_k_59_);
lean_ctor_set(v___x_87_, 0, v___x_133_);
v___x_135_ = v___x_87_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_l_61_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_l_76_);
v___x_135_ = v_reuseFailAlloc_148_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_isSharedCheck_142_ = !lean_is_exclusive(v_l_61_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; lean_object* v_unused_144_; lean_object* v_unused_145_; lean_object* v_unused_146_; lean_object* v_unused_147_; 
v_unused_143_ = lean_ctor_get(v_l_61_, 4);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_l_61_, 3);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_l_61_, 2);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_l_61_, 1);
lean_dec(v_unused_146_);
v_unused_147_ = lean_ctor_get(v_l_61_, 0);
lean_dec(v_unused_147_);
v___x_137_ = v_l_61_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_dec(v_l_61_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 4, v_r_77_);
lean_ctor_set(v___x_137_, 3, v___x_135_);
lean_ctor_set(v___x_137_, 2, v_v_75_);
lean_ctor_set(v___x_137_, 1, v_k_74_);
lean_ctor_set(v___x_137_, 0, v___x_132_);
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_74_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_75_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_r_77_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_155_; 
v_l_155_ = lean_ctor_get(v_impl_70_, 3);
lean_inc(v_l_155_);
if (lean_obj_tag(v_l_155_) == 0)
{
lean_object* v_r_156_; lean_object* v_k_157_; lean_object* v_v_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_181_; 
v_r_156_ = lean_ctor_get(v_impl_70_, 4);
v_k_157_ = lean_ctor_get(v_impl_70_, 1);
v_v_158_ = lean_ctor_get(v_impl_70_, 2);
v_isSharedCheck_181_ = !lean_is_exclusive(v_impl_70_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_182_ = lean_ctor_get(v_impl_70_, 3);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_impl_70_, 0);
lean_dec(v_unused_183_);
v___x_160_ = v_impl_70_;
v_isShared_161_ = v_isSharedCheck_181_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_r_156_);
lean_inc(v_v_158_);
lean_inc(v_k_157_);
lean_dec(v_impl_70_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_181_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_k_162_; lean_object* v_v_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_177_; 
v_k_162_ = lean_ctor_get(v_l_155_, 1);
v_v_163_ = lean_ctor_get(v_l_155_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v_l_155_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_178_ = lean_ctor_get(v_l_155_, 4);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_l_155_, 3);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_l_155_, 0);
lean_dec(v_unused_180_);
v___x_165_ = v_l_155_;
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_v_163_);
lean_inc(v_k_162_);
lean_dec(v_l_155_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_156_, 2);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 4, v_r_156_);
lean_ctor_set(v___x_165_, 3, v_r_156_);
lean_ctor_set(v___x_165_, 2, v_v_60_);
lean_ctor_set(v___x_165_, 1, v_k_59_);
lean_ctor_set(v___x_165_, 0, v___x_71_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_r_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_r_156_);
v___x_169_ = v_reuseFailAlloc_176_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
lean_inc(v_r_156_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 3, v_r_156_);
lean_ctor_set(v___x_160_, 0, v___x_71_);
v___x_171_ = v___x_160_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_157_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_158_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_156_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v___x_171_);
lean_ctor_set(v___x_64_, 3, v___x_169_);
lean_ctor_set(v___x_64_, 2, v_v_163_);
lean_ctor_set(v___x_64_, 1, v_k_162_);
lean_ctor_set(v___x_64_, 0, v___x_167_);
v___x_173_ = v___x_64_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_k_162_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_v_163_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
else
{
lean_object* v_r_184_; 
v_r_184_ = lean_ctor_get(v_impl_70_, 4);
lean_inc(v_r_184_);
if (lean_obj_tag(v_r_184_) == 0)
{
lean_object* v_k_185_; lean_object* v_v_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_197_; 
v_k_185_ = lean_ctor_get(v_impl_70_, 1);
v_v_186_ = lean_ctor_get(v_impl_70_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_impl_70_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; lean_object* v_unused_199_; lean_object* v_unused_200_; 
v_unused_198_ = lean_ctor_get(v_impl_70_, 4);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_impl_70_, 3);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_impl_70_, 0);
lean_dec(v_unused_200_);
v___x_188_ = v_impl_70_;
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_v_186_);
lean_inc(v_k_185_);
lean_dec(v_impl_70_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_unsigned_to_nat(3u);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 4, v_l_155_);
lean_ctor_set(v___x_188_, 2, v_v_60_);
lean_ctor_set(v___x_188_, 1, v_k_59_);
lean_ctor_set(v___x_188_, 0, v___x_71_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_l_155_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_l_155_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_r_184_);
lean_ctor_set(v___x_64_, 3, v___x_192_);
lean_ctor_set(v___x_64_, 2, v_v_186_);
lean_ctor_set(v___x_64_, 1, v_k_185_);
lean_ctor_set(v___x_64_, 0, v___x_190_);
v___x_194_ = v___x_64_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_k_185_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_v_186_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_r_184_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(2u);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_impl_70_);
lean_ctor_set(v___x_64_, 3, v_r_184_);
lean_ctor_set(v___x_64_, 0, v___x_201_);
v___x_203_ = v___x_64_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_r_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_impl_70_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
else
{
lean_object* v___x_205_; lean_object* v___x_207_; 
lean_dec(v_v_60_);
lean_dec(v_k_59_);
v___x_205_ = lean_box_uint64(v_k_55_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 2, v_v_56_);
lean_ctor_set(v___x_64_, 1, v___x_205_);
v___x_207_ = v___x_64_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_size_58_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_56_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_l_61_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_r_62_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_impl_209_; lean_object* v___x_210_; 
lean_dec(v_size_58_);
v_impl_209_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_55_, v_v_56_, v_l_61_);
v___x_210_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_62_) == 0)
{
lean_object* v_size_211_; lean_object* v_size_212_; lean_object* v_k_213_; lean_object* v_v_214_; lean_object* v_l_215_; lean_object* v_r_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_size_211_ = lean_ctor_get(v_r_62_, 0);
v_size_212_ = lean_ctor_get(v_impl_209_, 0);
lean_inc(v_size_212_);
v_k_213_ = lean_ctor_get(v_impl_209_, 1);
lean_inc(v_k_213_);
v_v_214_ = lean_ctor_get(v_impl_209_, 2);
lean_inc(v_v_214_);
v_l_215_ = lean_ctor_get(v_impl_209_, 3);
lean_inc(v_l_215_);
v_r_216_ = lean_ctor_get(v_impl_209_, 4);
lean_inc(v_r_216_);
v___x_217_ = lean_unsigned_to_nat(3u);
v___x_218_ = lean_nat_mul(v___x_217_, v_size_211_);
v___x_219_ = lean_nat_dec_lt(v___x_218_, v_size_212_);
lean_dec(v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
lean_dec(v_r_216_);
lean_dec(v_l_215_);
lean_dec(v_v_214_);
lean_dec(v_k_213_);
v___x_220_ = lean_nat_add(v___x_210_, v_size_212_);
lean_dec(v_size_212_);
v___x_221_ = lean_nat_add(v___x_220_, v_size_211_);
lean_dec(v___x_220_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 3, v_impl_209_);
lean_ctor_set(v___x_64_, 0, v___x_221_);
v___x_223_ = v___x_64_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_impl_209_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_r_62_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
else
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_290_; 
v_isSharedCheck_290_ = !lean_is_exclusive(v_impl_209_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; 
v_unused_291_ = lean_ctor_get(v_impl_209_, 4);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_impl_209_, 3);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_impl_209_, 2);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_impl_209_, 1);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_impl_209_, 0);
lean_dec(v_unused_295_);
v___x_226_ = v_impl_209_;
v_isShared_227_ = v_isSharedCheck_290_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_impl_209_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_290_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_size_228_; lean_object* v_size_229_; lean_object* v_k_230_; lean_object* v_v_231_; lean_object* v_l_232_; lean_object* v_r_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_size_228_ = lean_ctor_get(v_l_215_, 0);
v_size_229_ = lean_ctor_get(v_r_216_, 0);
v_k_230_ = lean_ctor_get(v_r_216_, 1);
v_v_231_ = lean_ctor_get(v_r_216_, 2);
v_l_232_ = lean_ctor_get(v_r_216_, 3);
v_r_233_ = lean_ctor_get(v_r_216_, 4);
v___x_234_ = lean_unsigned_to_nat(2u);
v___x_235_ = lean_nat_mul(v___x_234_, v_size_228_);
v___x_236_ = lean_nat_dec_lt(v_size_229_, v___x_235_);
lean_dec(v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_265_; 
lean_inc(v_r_233_);
lean_inc(v_l_232_);
lean_inc(v_v_231_);
lean_inc(v_k_230_);
v_isSharedCheck_265_ = !lean_is_exclusive(v_r_216_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; 
v_unused_266_ = lean_ctor_get(v_r_216_, 4);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_r_216_, 3);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_r_216_, 2);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_r_216_, 1);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_r_216_, 0);
lean_dec(v_unused_270_);
v___x_238_ = v_r_216_;
v_isShared_239_ = v_isSharedCheck_265_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_r_216_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_265_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___x_253_; lean_object* v___y_255_; 
v___x_240_ = lean_nat_add(v___x_210_, v_size_212_);
lean_dec(v_size_212_);
v___x_241_ = lean_nat_add(v___x_240_, v_size_211_);
lean_dec(v___x_240_);
v___x_253_ = lean_nat_add(v___x_210_, v_size_228_);
if (lean_obj_tag(v_l_232_) == 0)
{
lean_object* v_size_263_; 
v_size_263_ = lean_ctor_get(v_l_232_, 0);
lean_inc(v_size_263_);
v___y_255_ = v_size_263_;
goto v___jp_254_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___y_255_ = v___x_264_;
goto v___jp_254_;
}
v___jp_242_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_nat_add(v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec(v___y_244_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 4, v_r_62_);
lean_ctor_set(v___x_238_, 3, v_r_233_);
lean_ctor_set(v___x_238_, 2, v_v_60_);
lean_ctor_set(v___x_238_, 1, v_k_59_);
lean_ctor_set(v___x_238_, 0, v___x_246_);
v___x_248_ = v___x_238_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_r_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_r_62_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 4, v___x_248_);
lean_ctor_set(v___x_226_, 3, v___y_243_);
lean_ctor_set(v___x_226_, 2, v_v_231_);
lean_ctor_set(v___x_226_, 1, v_k_230_);
lean_ctor_set(v___x_226_, 0, v___x_241_);
v___x_250_ = v___x_226_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_k_230_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_v_231_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v___y_243_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_nat_add(v___x_253_, v___y_255_);
lean_dec(v___y_255_);
lean_dec(v___x_253_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_l_232_);
lean_ctor_set(v___x_64_, 3, v_l_215_);
lean_ctor_set(v___x_64_, 2, v_v_214_);
lean_ctor_set(v___x_64_, 1, v_k_213_);
lean_ctor_set(v___x_64_, 0, v___x_256_);
v___x_258_ = v___x_64_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_213_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_214_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_l_215_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_l_232_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = lean_nat_add(v___x_210_, v_size_211_);
if (lean_obj_tag(v_r_233_) == 0)
{
lean_object* v_size_260_; 
v_size_260_ = lean_ctor_get(v_r_233_, 0);
lean_inc(v_size_260_);
v___y_243_ = v___x_258_;
v___y_244_ = v___x_259_;
v___y_245_ = v_size_260_;
goto v___jp_242_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___y_243_ = v___x_258_;
v___y_244_ = v___x_259_;
v___y_245_ = v___x_261_;
goto v___jp_242_;
}
}
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_del_object(v___x_64_);
v___x_271_ = lean_nat_add(v___x_210_, v_size_212_);
lean_dec(v_size_212_);
v___x_272_ = lean_nat_add(v___x_271_, v_size_211_);
lean_dec(v___x_271_);
v___x_273_ = lean_nat_add(v___x_210_, v_size_211_);
v___x_274_ = lean_nat_add(v___x_273_, v_size_229_);
lean_dec(v___x_273_);
lean_inc_ref(v_r_62_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 4, v_r_62_);
lean_ctor_set(v___x_226_, 3, v_r_216_);
lean_ctor_set(v___x_226_, 2, v_v_60_);
lean_ctor_set(v___x_226_, 1, v_k_59_);
lean_ctor_set(v___x_226_, 0, v___x_274_);
v___x_276_ = v___x_226_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_r_216_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_r_62_);
v___x_276_ = v_reuseFailAlloc_289_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_isSharedCheck_283_ = !lean_is_exclusive(v_r_62_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_284_ = lean_ctor_get(v_r_62_, 4);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_r_62_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_r_62_, 2);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_r_62_, 1);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_r_62_, 0);
lean_dec(v_unused_288_);
v___x_278_ = v_r_62_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_dec(v_r_62_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 4, v___x_276_);
lean_ctor_set(v___x_278_, 3, v_l_215_);
lean_ctor_set(v___x_278_, 2, v_v_214_);
lean_ctor_set(v___x_278_, 1, v_k_213_);
lean_ctor_set(v___x_278_, 0, v___x_272_);
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_213_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_214_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_l_215_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v___x_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_296_; 
v_l_296_ = lean_ctor_get(v_impl_209_, 3);
lean_inc(v_l_296_);
if (lean_obj_tag(v_l_296_) == 0)
{
lean_object* v_r_297_; lean_object* v_k_298_; lean_object* v_v_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
v_r_297_ = lean_ctor_get(v_impl_209_, 4);
v_k_298_ = lean_ctor_get(v_impl_209_, 1);
v_v_299_ = lean_ctor_get(v_impl_209_, 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v_impl_209_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_311_ = lean_ctor_get(v_impl_209_, 3);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_impl_209_, 0);
lean_dec(v_unused_312_);
v___x_301_ = v_impl_209_;
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_r_297_);
lean_inc(v_v_299_);
lean_inc(v_k_298_);
lean_dec(v_impl_209_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_297_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v_r_297_);
lean_ctor_set(v___x_301_, 2, v_v_60_);
lean_ctor_set(v___x_301_, 1, v_k_59_);
lean_ctor_set(v___x_301_, 0, v___x_210_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_r_297_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_r_297_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v___x_305_);
lean_ctor_set(v___x_64_, 3, v_l_296_);
lean_ctor_set(v___x_64_, 2, v_v_299_);
lean_ctor_set(v___x_64_, 1, v_k_298_);
lean_ctor_set(v___x_64_, 0, v___x_303_);
v___x_307_ = v___x_64_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_v_299_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_l_296_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v_r_313_; 
v_r_313_ = lean_ctor_get(v_impl_209_, 4);
lean_inc(v_r_313_);
if (lean_obj_tag(v_r_313_) == 0)
{
lean_object* v_k_314_; lean_object* v_v_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_338_; 
v_k_314_ = lean_ctor_get(v_impl_209_, 1);
v_v_315_ = lean_ctor_get(v_impl_209_, 2);
v_isSharedCheck_338_ = !lean_is_exclusive(v_impl_209_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; lean_object* v_unused_341_; 
v_unused_339_ = lean_ctor_get(v_impl_209_, 4);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_impl_209_, 3);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_impl_209_, 0);
lean_dec(v_unused_341_);
v___x_317_ = v_impl_209_;
v_isShared_318_ = v_isSharedCheck_338_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_v_315_);
lean_inc(v_k_314_);
lean_dec(v_impl_209_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_338_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_334_; 
v_k_319_ = lean_ctor_get(v_r_313_, 1);
v_v_320_ = lean_ctor_get(v_r_313_, 2);
v_isSharedCheck_334_ = !lean_is_exclusive(v_r_313_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; lean_object* v_unused_336_; lean_object* v_unused_337_; 
v_unused_335_ = lean_ctor_get(v_r_313_, 4);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_r_313_, 3);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_r_313_, 0);
lean_dec(v_unused_337_);
v___x_322_ = v_r_313_;
v_isShared_323_ = v_isSharedCheck_334_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_v_320_);
lean_inc(v_k_319_);
lean_dec(v_r_313_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_334_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(3u);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 4, v_l_296_);
lean_ctor_set(v___x_322_, 3, v_l_296_);
lean_ctor_set(v___x_322_, 2, v_v_315_);
lean_ctor_set(v___x_322_, 1, v_k_314_);
lean_ctor_set(v___x_322_, 0, v___x_210_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_k_314_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_v_315_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_l_296_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_l_296_);
v___x_326_ = v_reuseFailAlloc_333_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 4, v_l_296_);
lean_ctor_set(v___x_317_, 2, v_v_60_);
lean_ctor_set(v___x_317_, 1, v_k_59_);
lean_ctor_set(v___x_317_, 0, v___x_210_);
v___x_328_ = v___x_317_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_l_296_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_l_296_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v___x_328_);
lean_ctor_set(v___x_64_, 3, v___x_326_);
lean_ctor_set(v___x_64_, 2, v_v_320_);
lean_ctor_set(v___x_64_, 1, v_k_319_);
lean_ctor_set(v___x_64_, 0, v___x_324_);
v___x_330_ = v___x_64_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_unsigned_to_nat(2u);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 4, v_r_313_);
lean_ctor_set(v___x_64_, 3, v_impl_209_);
lean_ctor_set(v___x_64_, 0, v___x_342_);
v___x_344_ = v___x_64_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_60_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_impl_209_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_r_313_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_box_uint64(v_k_55_);
v___x_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_ctor_set(v___x_349_, 2, v_v_56_);
lean_ctor_set(v___x_349_, 3, v_t_57_);
lean_ctor_set(v___x_349_, 4, v_t_57_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg___boxed(lean_object* v_k_350_, lean_object* v_v_351_, lean_object* v_t_352_){
_start:
{
uint64_t v_k_boxed_353_; lean_object* v_res_354_; 
v_k_boxed_353_ = lean_unbox_uint64(v_k_350_);
lean_dec_ref(v_k_350_);
v_res_354_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_boxed_353_, v_v_351_, v_t_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addBuiltinModule(lean_object* v_id_355_, lean_object* v_m_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; uint64_t v_javascriptHash_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_358_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_359_ = lean_st_ref_take(v___x_358_);
v_javascriptHash_360_ = lean_ctor_get_uint64(v_m_356_, sizeof(void*)*1);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_id_355_);
lean_ctor_set(v___x_361_, 1, v_m_356_);
v___x_362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_javascriptHash_360_, v___x_361_, v___x_359_);
v___x_363_ = lean_st_ref_set(v___x_358_, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addBuiltinModule___boxed(lean_object* v_id_365_, lean_object* v_m_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Widget_addBuiltinModule(v_id_365_, v_m_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0(lean_object* v_00_u03b2_369_, uint64_t v_k_370_, lean_object* v_v_371_, lean_object* v_t_372_, lean_object* v_hl_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_370_, v_v_371_, v_t_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___boxed(lean_object* v_00_u03b2_375_, lean_object* v_k_376_, lean_object* v_v_377_, lean_object* v_t_378_, lean_object* v_hl_379_){
_start:
{
uint64_t v_k_boxed_380_; lean_object* v_res_381_; 
v_k_boxed_380_ = lean_unbox_uint64(v_k_376_);
lean_dec_ref(v_k_376_);
v_res_381_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0(v_00_u03b2_375_, v_k_boxed_380_, v_v_377_, v_t_378_, v_hl_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v_s_382_, lean_object* v_n_383_){
_start:
{
lean_object* v_fst_384_; lean_object* v_snd_385_; uint64_t v___x_386_; lean_object* v___x_387_; 
v_fst_384_ = lean_ctor_get(v_n_383_, 0);
lean_inc(v_fst_384_);
v_snd_385_ = lean_ctor_get(v_n_383_, 1);
lean_inc(v_snd_385_);
lean_dec_ref(v_n_383_);
v___x_386_ = lean_unbox_uint64(v_fst_384_);
lean_dec(v_fst_384_);
v___x_387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_386_, v_snd_385_, v_s_382_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v_es_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_array_mk(v_es_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_390_, size_t v_i_391_, size_t v_stop_392_, lean_object* v_b_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_391_, v_stop_392_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v_fst_396_; lean_object* v_snd_397_; uint64_t v___x_398_; lean_object* v___x_399_; size_t v___x_400_; size_t v___x_401_; 
v___x_395_ = lean_array_uget_borrowed(v_as_390_, v_i_391_);
v_fst_396_ = lean_ctor_get(v___x_395_, 0);
v_snd_397_ = lean_ctor_get(v___x_395_, 1);
v___x_398_ = lean_unbox_uint64(v_fst_396_);
lean_inc(v_snd_397_);
v___x_399_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_398_, v_snd_397_, v_b_393_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_391_, v___x_400_);
v_i_391_ = v___x_401_;
v_b_393_ = v___x_399_;
goto _start;
}
else
{
return v_b_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_403_, lean_object* v_i_404_, lean_object* v_stop_405_, lean_object* v_b_406_){
_start:
{
size_t v_i_boxed_407_; size_t v_stop_boxed_408_; lean_object* v_res_409_; 
v_i_boxed_407_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_stop_boxed_408_ = lean_unbox_usize(v_stop_405_);
lean_dec(v_stop_405_);
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(v_as_403_, v_i_boxed_407_, v_stop_boxed_408_, v_b_406_);
lean_dec_ref(v_as_403_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(lean_object* v_as_410_, size_t v_i_411_, size_t v_stop_412_, lean_object* v_b_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_eq(v_i_411_, v_stop_412_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; uint64_t v___x_418_; lean_object* v___x_419_; size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
v___x_415_ = lean_array_uget_borrowed(v_as_410_, v_i_411_);
v_fst_416_ = lean_ctor_get(v___x_415_, 0);
v_snd_417_ = lean_ctor_get(v___x_415_, 1);
v___x_418_ = lean_unbox_uint64(v_fst_416_);
lean_inc(v_snd_417_);
v___x_419_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_418_, v_snd_417_, v_b_413_);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_411_, v___x_420_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(v_as_410_, v___x_421_, v_stop_412_, v___x_419_);
return v___x_422_;
}
else
{
return v_b_413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_423_, lean_object* v_i_424_, lean_object* v_stop_425_, lean_object* v_b_426_){
_start:
{
size_t v_i_boxed_427_; size_t v_stop_boxed_428_; lean_object* v_res_429_; 
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_stop_boxed_428_ = lean_unbox_usize(v_stop_425_);
lean_dec(v_stop_425_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v_as_423_, v_i_boxed_427_, v_stop_boxed_428_, v_b_426_);
lean_dec_ref(v_as_423_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(lean_object* v_as_430_, size_t v_i_431_, size_t v_stop_432_, lean_object* v_b_433_){
_start:
{
lean_object* v___y_435_; uint8_t v___x_439_; 
v___x_439_ = lean_usize_dec_eq(v_i_431_, v_stop_432_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_array_uget_borrowed(v_as_430_, v_i_431_);
v___x_442_ = lean_array_get_size(v___x_441_);
v___x_443_ = lean_nat_dec_lt(v___x_440_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_435_ = v_b_433_;
goto v___jp_434_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v___x_442_, v___x_442_);
if (v___x_444_ == 0)
{
if (v___x_443_ == 0)
{
v___y_435_ = v_b_433_;
goto v___jp_434_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_442_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v___x_441_, v___x_445_, v___x_446_, v_b_433_);
v___y_435_ = v___x_447_;
goto v___jp_434_;
}
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_442_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v___x_441_, v___x_448_, v___x_449_, v_b_433_);
v___y_435_ = v___x_450_;
goto v___jp_434_;
}
}
}
else
{
return v_b_433_;
}
v___jp_434_:
{
size_t v___x_436_; size_t v___x_437_; 
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_431_, v___x_436_);
v_i_431_ = v___x_437_;
v_b_433_ = v___y_435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_451_, lean_object* v_i_452_, lean_object* v_stop_453_, lean_object* v_b_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; lean_object* v_res_457_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_453_);
lean_dec(v_stop_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_as_451_, v_i_boxed_455_, v_stop_boxed_456_, v_b_454_);
lean_dec_ref(v_as_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v___x_458_, lean_object* v_xss_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_box(1);
v___x_461_ = lean_array_get_size(v_xss_459_);
v___x_462_ = lean_nat_dec_lt(v___x_458_, v___x_461_);
if (v___x_462_ == 0)
{
return v___x_460_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = lean_nat_dec_le(v___x_461_, v___x_461_);
if (v___x_463_ == 0)
{
if (v___x_462_ == 0)
{
return v___x_460_;
}
else
{
size_t v___x_464_; size_t v___x_465_; lean_object* v___x_466_; 
v___x_464_ = ((size_t)0ULL);
v___x_465_ = lean_usize_of_nat(v___x_461_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_xss_459_, v___x_464_, v___x_465_, v___x_460_);
return v___x_466_;
}
}
else
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((size_t)0ULL);
v___x_468_ = lean_usize_of_nat(v___x_461_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_xss_459_, v___x_467_, v___x_468_, v___x_460_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v___x_470_, lean_object* v_xss_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(v___x_470_, v_xss_471_);
lean_dec_ref(v_xss_471_);
lean_dec(v___x_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_));
v___x_513_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
return v_res_515_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_516_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_522_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_ctor_set(v___x_522_, 3, v___x_521_);
lean_ctor_set(v___x_522_, 4, v___x_521_);
lean_ctor_set(v___x_522_, 5, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_nextMacroScope_528_; lean_object* v_ngen_529_; lean_object* v_auxDeclNGen_530_; lean_object* v_traceState_531_; lean_object* v_messages_532_; lean_object* v_infoState_533_; lean_object* v_snapshotTasks_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_560_; 
v___x_527_ = lean_st_ref_take(v___y_525_);
v_nextMacroScope_528_ = lean_ctor_get(v___x_527_, 1);
v_ngen_529_ = lean_ctor_get(v___x_527_, 2);
v_auxDeclNGen_530_ = lean_ctor_get(v___x_527_, 3);
v_traceState_531_ = lean_ctor_get(v___x_527_, 4);
v_messages_532_ = lean_ctor_get(v___x_527_, 6);
v_infoState_533_ = lean_ctor_get(v___x_527_, 7);
v_snapshotTasks_534_ = lean_ctor_get(v___x_527_, 8);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; lean_object* v_unused_562_; 
v_unused_561_ = lean_ctor_get(v___x_527_, 5);
lean_dec(v_unused_561_);
v_unused_562_ = lean_ctor_get(v___x_527_, 0);
lean_dec(v_unused_562_);
v___x_536_ = v___x_527_;
v_isShared_537_ = v_isSharedCheck_560_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snapshotTasks_534_);
lean_inc(v_infoState_533_);
lean_inc(v_messages_532_);
lean_inc(v_traceState_531_);
lean_inc(v_auxDeclNGen_530_);
lean_inc(v_ngen_529_);
lean_inc(v_nextMacroScope_528_);
lean_dec(v___x_527_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_560_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 5, v___x_538_);
lean_ctor_set(v___x_536_, 0, v_env_523_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_env_523_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_nextMacroScope_528_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_ngen_529_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_auxDeclNGen_530_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_traceState_531_);
lean_ctor_set(v_reuseFailAlloc_559_, 5, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_559_, 6, v_messages_532_);
lean_ctor_set(v_reuseFailAlloc_559_, 7, v_infoState_533_);
lean_ctor_set(v_reuseFailAlloc_559_, 8, v_snapshotTasks_534_);
v___x_540_ = v_reuseFailAlloc_559_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_mctx_543_; lean_object* v_zetaDeltaFVarIds_544_; lean_object* v_postponed_545_; lean_object* v_diag_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_557_; 
v___x_541_ = lean_st_ref_set(v___y_525_, v___x_540_);
v___x_542_ = lean_st_ref_take(v___y_524_);
v_mctx_543_ = lean_ctor_get(v___x_542_, 0);
v_zetaDeltaFVarIds_544_ = lean_ctor_get(v___x_542_, 2);
v_postponed_545_ = lean_ctor_get(v___x_542_, 3);
v_diag_546_ = lean_ctor_get(v___x_542_, 4);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v___x_542_, 1);
lean_dec(v_unused_558_);
v___x_548_ = v___x_542_;
v_isShared_549_ = v_isSharedCheck_557_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_diag_546_);
lean_inc(v_postponed_545_);
lean_inc(v_zetaDeltaFVarIds_544_);
lean_inc(v_mctx_543_);
lean_dec(v___x_542_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_557_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_mctx_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_zetaDeltaFVarIds_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_postponed_545_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_diag_546_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_st_ref_set(v___y_524_, v___x_552_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(v_env_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec(v___y_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1(lean_object* v_env_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(v_env_568_, v___y_570_, v___y_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1(v_env_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_582_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_ctor_set(v___x_587_, 2, v___x_586_);
lean_ctor_set(v___x_587_, 3, v___x_585_);
lean_ctor_set(v___x_587_, 4, v___x_585_);
lean_ctor_set(v___x_587_, 5, v___x_585_);
lean_ctor_set(v___x_587_, 6, v___x_585_);
lean_ctor_set(v___x_587_, 7, v___x_585_);
lean_ctor_set(v___x_587_, 8, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_591_ = ((size_t)5ULL);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_unsigned_to_nat(32u);
v___x_594_ = lean_mk_empty_array_with_capacity(v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_596_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___x_592_);
lean_ctor_set(v___x_596_, 3, v___x_592_);
lean_ctor_set_usize(v___x_596_, 4, v___x_591_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_box(1);
v___x_598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v_options_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
v_options_607_ = lean_ctor_get(v___y_602_, 2);
v___x_608_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_607_);
v___x_610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_610_, 0, v_env_606_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_609_);
lean_ctor_set(v___x_610_, 3, v_options_607_);
v___x_611_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_msgData_601_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(v_msgData_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_ref_622_; lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_ref_622_ = lean_ctor_get(v___y_619_, 5);
v___x_623_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(v_msg_618_, v___y_619_, v___y_620_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
lean_inc(v_ref_622_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_ref_622_);
lean_ctor_set(v___x_628_, 1, v_a_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v_msg_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v_name_644_, lean_object* v_decl_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = lean_obj_once(&l_Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_650_ = l_Lean_MessageData_ofName(v_name_644_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v___x_653_, v___y_646_, v___y_647_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_name_655_, lean_object* v_decl_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v_name_655_, v_decl_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_decl_656_);
return v_res_660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_opts_661_, lean_object* v_opt_662_){
_start:
{
lean_object* v_name_663_; lean_object* v_defValue_664_; lean_object* v_map_665_; lean_object* v___x_666_; 
v_name_663_ = lean_ctor_get(v_opt_662_, 0);
v_defValue_664_ = lean_ctor_get(v_opt_662_, 1);
v_map_665_ = lean_ctor_get(v_opts_661_, 0);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_665_, v_name_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
uint8_t v___x_667_; 
v___x_667_ = lean_unbox(v_defValue_664_);
return v___x_667_;
}
else
{
lean_object* v_val_668_; 
v_val_668_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_668_);
lean_dec_ref(v___x_666_);
if (lean_obj_tag(v_val_668_) == 1)
{
uint8_t v_v_669_; 
v_v_669_ = lean_ctor_get_uint8(v_val_668_, 0);
lean_dec_ref(v_val_668_);
return v_v_669_;
}
else
{
uint8_t v___x_670_; 
lean_dec(v_val_668_);
v___x_670_ = lean_unbox(v_defValue_664_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_opts_671_, lean_object* v_opt_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_opts_671_, v_opt_672_);
lean_dec_ref(v_opt_672_);
lean_dec_ref(v_opts_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t v___y_683_, uint8_t v_suppressElabErrors_684_, lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_685_) == 1)
{
lean_object* v_pre_686_; 
v_pre_686_ = lean_ctor_get(v_x_685_, 0);
switch(lean_obj_tag(v_pre_686_))
{
case 1:
{
lean_object* v_pre_687_; 
v_pre_687_ = lean_ctor_get(v_pre_686_, 0);
switch(lean_obj_tag(v_pre_687_))
{
case 0:
{
lean_object* v_str_688_; lean_object* v_str_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_str_688_ = lean_ctor_get(v_x_685_, 1);
v_str_689_ = lean_ctor_get(v_pre_686_, 1);
v___x_690_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_691_ = lean_string_dec_eq(v_str_689_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_693_ = lean_string_dec_eq(v_str_689_, v___x_692_);
if (v___x_693_ == 0)
{
return v___y_683_;
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_695_ = lean_string_dec_eq(v_str_688_, v___x_694_);
if (v___x_695_ == 0)
{
return v___y_683_;
}
else
{
return v_suppressElabErrors_684_;
}
}
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_697_ = lean_string_dec_eq(v_str_688_, v___x_696_);
if (v___x_697_ == 0)
{
return v___y_683_;
}
else
{
return v_suppressElabErrors_684_;
}
}
}
case 1:
{
lean_object* v_pre_698_; 
v_pre_698_ = lean_ctor_get(v_pre_687_, 0);
if (lean_obj_tag(v_pre_698_) == 0)
{
lean_object* v_str_699_; lean_object* v_str_700_; lean_object* v_str_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_str_699_ = lean_ctor_get(v_x_685_, 1);
v_str_700_ = lean_ctor_get(v_pre_686_, 1);
v_str_701_ = lean_ctor_get(v_pre_687_, 1);
v___x_702_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_703_ = lean_string_dec_eq(v_str_701_, v___x_702_);
if (v___x_703_ == 0)
{
return v___y_683_;
}
else
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_705_ = lean_string_dec_eq(v_str_700_, v___x_704_);
if (v___x_705_ == 0)
{
return v___y_683_;
}
else
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6));
v___x_707_ = lean_string_dec_eq(v_str_699_, v___x_706_);
if (v___x_707_ == 0)
{
return v___y_683_;
}
else
{
return v_suppressElabErrors_684_;
}
}
}
}
else
{
return v___y_683_;
}
}
default: 
{
return v___y_683_;
}
}
}
case 0:
{
lean_object* v_str_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_str_708_ = lean_ctor_get(v_x_685_, 1);
v___x_709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7));
v___x_710_ = lean_string_dec_eq(v_str_708_, v___x_709_);
if (v___x_710_ == 0)
{
return v___y_683_;
}
else
{
return v_suppressElabErrors_684_;
}
}
default: 
{
return v___y_683_;
}
}
}
else
{
return v___y_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___y_711_, lean_object* v_suppressElabErrors_712_, lean_object* v_x_713_){
_start:
{
uint8_t v___y_11607__boxed_714_; uint8_t v_suppressElabErrors_boxed_715_; uint8_t v_res_716_; lean_object* v_r_717_; 
v___y_11607__boxed_714_ = lean_unbox(v___y_711_);
v_suppressElabErrors_boxed_715_ = lean_unbox(v_suppressElabErrors_712_);
v_res_716_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v___y_11607__boxed_714_, v_suppressElabErrors_boxed_715_, v_x_713_);
lean_dec(v_x_713_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_msgData_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_env_725_; lean_object* v___x_726_; lean_object* v_mctx_727_; lean_object* v_lctx_728_; lean_object* v_options_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_724_ = lean_st_ref_get(v___y_722_);
v_env_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_env_725_);
lean_dec(v___x_724_);
v___x_726_ = lean_st_ref_get(v___y_720_);
v_mctx_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_mctx_727_);
lean_dec(v___x_726_);
v_lctx_728_ = lean_ctor_get(v___y_719_, 2);
v_options_729_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref(v_options_729_);
lean_inc_ref(v_lctx_728_);
v___x_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_730_, 0, v_env_725_);
lean_ctor_set(v___x_730_, 1, v_mctx_727_);
lean_ctor_set(v___x_730_, 2, v_lctx_728_);
lean_ctor_set(v___x_730_, 3, v_options_729_);
v___x_731_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_msgData_718_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msgData_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_ref_741_, lean_object* v_msgData_742_, uint8_t v_severity_743_, uint8_t v_isSilent_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_787_; uint8_t v___y_788_; lean_object* v___y_789_; uint8_t v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; uint8_t v___y_818_; lean_object* v___y_819_; lean_object* v___y_823_; uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; uint8_t v___y_828_; uint8_t v___y_829_; uint8_t v___x_834_; lean_object* v___y_836_; lean_object* v___y_837_; uint8_t v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; uint8_t v___y_842_; uint8_t v___y_844_; uint8_t v___x_859_; 
v___x_834_ = 2;
v___x_859_ = l_Lean_instBEqMessageSeverity_beq(v_severity_743_, v___x_834_);
if (v___x_859_ == 0)
{
v___y_844_ = v___x_859_;
goto v___jp_843_;
}
else
{
uint8_t v___x_860_; 
lean_inc_ref(v_msgData_742_);
v___x_860_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_742_);
v___y_844_ = v___x_860_;
goto v___jp_843_;
}
v___jp_750_:
{
lean_object* v___x_760_; lean_object* v_currNamespace_761_; lean_object* v_openDecls_762_; lean_object* v_env_763_; lean_object* v_nextMacroScope_764_; lean_object* v_ngen_765_; lean_object* v_auxDeclNGen_766_; lean_object* v_traceState_767_; lean_object* v_cache_768_; lean_object* v_messages_769_; lean_object* v_infoState_770_; lean_object* v_snapshotTasks_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_785_; 
v___x_760_ = lean_st_ref_take(v___y_759_);
v_currNamespace_761_ = lean_ctor_get(v___y_758_, 6);
lean_inc(v_currNamespace_761_);
v_openDecls_762_ = lean_ctor_get(v___y_758_, 7);
lean_inc(v_openDecls_762_);
lean_dec_ref(v___y_758_);
v_env_763_ = lean_ctor_get(v___x_760_, 0);
v_nextMacroScope_764_ = lean_ctor_get(v___x_760_, 1);
v_ngen_765_ = lean_ctor_get(v___x_760_, 2);
v_auxDeclNGen_766_ = lean_ctor_get(v___x_760_, 3);
v_traceState_767_ = lean_ctor_get(v___x_760_, 4);
v_cache_768_ = lean_ctor_get(v___x_760_, 5);
v_messages_769_ = lean_ctor_get(v___x_760_, 6);
v_infoState_770_ = lean_ctor_get(v___x_760_, 7);
v_snapshotTasks_771_ = lean_ctor_get(v___x_760_, 8);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_785_ == 0)
{
v___x_773_ = v___x_760_;
v_isShared_774_ = v_isSharedCheck_785_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_snapshotTasks_771_);
lean_inc(v_infoState_770_);
lean_inc(v_messages_769_);
lean_inc(v_cache_768_);
lean_inc(v_traceState_767_);
lean_inc(v_auxDeclNGen_766_);
lean_inc(v_ngen_765_);
lean_inc(v_nextMacroScope_764_);
lean_inc(v_env_763_);
lean_dec(v___x_760_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_785_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_currNamespace_761_);
lean_ctor_set(v___x_775_, 1, v_openDecls_762_);
v___x_776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___y_757_);
v___x_777_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_777_, 0, v___y_755_);
lean_ctor_set(v___x_777_, 1, v___y_751_);
lean_ctor_set(v___x_777_, 2, v___y_752_);
lean_ctor_set(v___x_777_, 3, v___y_753_);
lean_ctor_set(v___x_777_, 4, v___x_776_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*5, v___y_756_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*5 + 1, v___y_754_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*5 + 2, v_isSilent_744_);
v___x_778_ = l_Lean_MessageLog_add(v___x_777_, v_messages_769_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 6, v___x_778_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_env_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_nextMacroScope_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_ngen_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_auxDeclNGen_766_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_traceState_767_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_cache_768_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_infoState_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_snapshotTasks_771_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_st_ref_set(v___y_759_, v___x_780_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
v___jp_786_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_810_; 
v___x_795_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_742_);
v___x_796_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(v___x_795_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_810_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_inc_ref(v___y_791_);
v___x_801_ = l_Lean_FileMap_toPosition(v___y_791_, v___y_793_);
lean_dec(v___y_793_);
v___x_802_ = l_Lean_FileMap_toPosition(v___y_791_, v___y_794_);
lean_dec(v___y_794_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
if (v___y_788_ == 0)
{
lean_del_object(v___x_799_);
lean_dec_ref(v___y_787_);
v___y_751_ = v___x_801_;
v___y_752_ = v___x_803_;
v___y_753_ = v___x_804_;
v___y_754_ = v___y_790_;
v___y_755_ = v___y_789_;
v___y_756_ = v___y_792_;
v___y_757_ = v_a_797_;
v___y_758_ = v___y_747_;
v___y_759_ = v___y_748_;
goto v___jp_750_;
}
else
{
uint8_t v___x_805_; 
lean_inc(v_a_797_);
v___x_805_ = l_Lean_MessageData_hasTag(v___y_787_, v_a_797_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec_ref(v___x_803_);
lean_dec_ref(v___x_801_);
lean_dec(v_a_797_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v___y_747_);
v___x_806_ = lean_box(0);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_del_object(v___x_799_);
v___y_751_ = v___x_801_;
v___y_752_ = v___x_803_;
v___y_753_ = v___x_804_;
v___y_754_ = v___y_790_;
v___y_755_ = v___y_789_;
v___y_756_ = v___y_792_;
v___y_757_ = v_a_797_;
v___y_758_ = v___y_747_;
v___y_759_ = v___y_748_;
goto v___jp_750_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Syntax_getTailPos_x3f(v___y_814_, v___y_818_);
lean_dec(v___y_814_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_inc(v___y_819_);
v___y_787_ = v___y_812_;
v___y_788_ = v___y_813_;
v___y_789_ = v___y_816_;
v___y_790_ = v___y_815_;
v___y_791_ = v___y_817_;
v___y_792_ = v___y_818_;
v___y_793_ = v___y_819_;
v___y_794_ = v___y_819_;
goto v___jp_786_;
}
else
{
lean_object* v_val_821_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref(v___x_820_);
v___y_787_ = v___y_812_;
v___y_788_ = v___y_813_;
v___y_789_ = v___y_816_;
v___y_790_ = v___y_815_;
v___y_791_ = v___y_817_;
v___y_792_ = v___y_818_;
v___y_793_ = v___y_819_;
v___y_794_ = v_val_821_;
goto v___jp_786_;
}
}
v___jp_822_:
{
lean_object* v_ref_830_; lean_object* v___x_831_; 
v_ref_830_ = l_Lean_replaceRef(v_ref_741_, v___y_825_);
lean_dec(v___y_825_);
v___x_831_ = l_Lean_Syntax_getPos_x3f(v_ref_830_, v___y_828_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___y_812_ = v___y_823_;
v___y_813_ = v___y_824_;
v___y_814_ = v_ref_830_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_826_;
v___y_817_ = v___y_827_;
v___y_818_ = v___y_828_;
v___y_819_ = v___x_832_;
goto v___jp_811_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v___x_831_);
v___y_812_ = v___y_823_;
v___y_813_ = v___y_824_;
v___y_814_ = v_ref_830_;
v___y_815_ = v___y_829_;
v___y_816_ = v___y_826_;
v___y_817_ = v___y_827_;
v___y_818_ = v___y_828_;
v___y_819_ = v_val_833_;
goto v___jp_811_;
}
}
v___jp_835_:
{
if (v___y_842_ == 0)
{
v___y_823_ = v___y_836_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_837_;
v___y_826_ = v___y_839_;
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v___y_829_ = v_severity_743_;
goto v___jp_822_;
}
else
{
v___y_823_ = v___y_836_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_837_;
v___y_826_ = v___y_839_;
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v___y_829_ = v___x_834_;
goto v___jp_822_;
}
}
v___jp_843_:
{
if (v___y_844_ == 0)
{
lean_object* v_fileName_845_; lean_object* v_fileMap_846_; lean_object* v_options_847_; lean_object* v_ref_848_; uint8_t v_suppressElabErrors_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___f_852_; uint8_t v___x_853_; uint8_t v___x_854_; 
v_fileName_845_ = lean_ctor_get(v___y_747_, 0);
v_fileMap_846_ = lean_ctor_get(v___y_747_, 1);
v_options_847_ = lean_ctor_get(v___y_747_, 2);
v_ref_848_ = lean_ctor_get(v___y_747_, 5);
v_suppressElabErrors_849_ = lean_ctor_get_uint8(v___y_747_, sizeof(void*)*14 + 1);
v___x_850_ = lean_box(v___y_844_);
v___x_851_ = lean_box(v_suppressElabErrors_849_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_852_, 0, v___x_850_);
lean_closure_set(v___f_852_, 1, v___x_851_);
v___x_853_ = 1;
v___x_854_ = l_Lean_instBEqMessageSeverity_beq(v_severity_743_, v___x_853_);
if (v___x_854_ == 0)
{
lean_inc_ref(v_fileMap_846_);
lean_inc_ref(v_fileName_845_);
lean_inc(v_ref_848_);
v___y_836_ = v___f_852_;
v___y_837_ = v_ref_848_;
v___y_838_ = v_suppressElabErrors_849_;
v___y_839_ = v_fileName_845_;
v___y_840_ = v_fileMap_846_;
v___y_841_ = v___y_844_;
v___y_842_ = v___x_854_;
goto v___jp_835_;
}
else
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = l_Lean_warningAsError;
v___x_856_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_options_847_, v___x_855_);
lean_inc_ref(v_fileMap_846_);
lean_inc_ref(v_fileName_845_);
lean_inc(v_ref_848_);
v___y_836_ = v___f_852_;
v___y_837_ = v_ref_848_;
v___y_838_ = v_suppressElabErrors_849_;
v___y_839_ = v_fileName_845_;
v___y_840_ = v_fileMap_846_;
v___y_841_ = v___y_844_;
v___y_842_ = v___x_856_;
goto v___jp_835_;
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v___y_747_);
lean_dec_ref(v_msgData_742_);
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_ref_861_, lean_object* v_msgData_862_, lean_object* v_severity_863_, lean_object* v_isSilent_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_severity_boxed_870_; uint8_t v_isSilent_boxed_871_; lean_object* v_res_872_; 
v_severity_boxed_870_ = lean_unbox(v_severity_863_);
v_isSilent_boxed_871_ = lean_unbox(v_isSilent_864_);
v_res_872_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_861_, v_msgData_862_, v_severity_boxed_870_, v_isSilent_boxed_871_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v_ref_861_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_msgData_873_, uint8_t v_severity_874_, uint8_t v_isSilent_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_ref_881_; lean_object* v___x_882_; 
v_ref_881_ = lean_ctor_get(v___y_878_, 5);
lean_inc(v_ref_881_);
v___x_882_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_881_, v_msgData_873_, v_severity_874_, v_isSilent_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v_ref_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_msgData_883_, lean_object* v_severity_884_, lean_object* v_isSilent_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_severity_boxed_891_; uint8_t v_isSilent_boxed_892_; lean_object* v_res_893_; 
v_severity_boxed_891_ = lean_unbox(v_severity_884_);
v_isSilent_boxed_892_ = lean_unbox(v_isSilent_885_);
v_res_893_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(v_msgData_883_, v_severity_boxed_891_, v_isSilent_boxed_892_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(lean_object* v_msgData_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; 
v___x_900_ = 1;
v___x_901_ = 0;
v___x_902_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(v_msgData_894_, v___x_900_, v___x_901_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3___boxed(lean_object* v_msgData_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(v_msgData_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_msg_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_ref_916_; lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_ref_916_ = lean_ctor_get(v___y_913_, 5);
v___x_917_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msg_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_inc(v_ref_916_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_ref_916_);
lean_ctor_set(v___x_922_, 1, v_a_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 1);
lean_ctor_set(v___x_920_, 0, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_946_, uint8_t v_kind_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___y_959_; 
v___x_953_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_954_ = l_Lean_MessageData_ofName(v_name_946_);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
switch(v_kind_947_)
{
case 0:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_959_ = v___x_966_;
goto v___jp_958_;
}
case 1:
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_959_ = v___x_967_;
goto v___jp_958_;
}
default: 
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_959_ = v___x_968_;
goto v___jp_958_;
}
}
v___jp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___y_959_);
v___x_961_ = l_Lean_MessageData_ofFormat(v___x_960_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_957_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_964_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_969_, lean_object* v_kind_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v_kind_boxed_976_; lean_object* v_res_977_; 
v_kind_boxed_976_ = lean_unbox(v_kind_970_);
v_res_977_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_969_, v_kind_boxed_976_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_978_, uint64_t v_k_979_){
_start:
{
if (lean_obj_tag(v_t_978_) == 0)
{
lean_object* v_k_980_; lean_object* v_v_981_; lean_object* v_l_982_; lean_object* v_r_983_; uint64_t v___x_984_; uint8_t v___x_985_; 
v_k_980_ = lean_ctor_get(v_t_978_, 1);
v_v_981_ = lean_ctor_get(v_t_978_, 2);
v_l_982_ = lean_ctor_get(v_t_978_, 3);
v_r_983_ = lean_ctor_get(v_t_978_, 4);
v___x_984_ = lean_unbox_uint64(v_k_980_);
v___x_985_ = lean_uint64_dec_lt(v_k_979_, v___x_984_);
if (v___x_985_ == 0)
{
uint64_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_unbox_uint64(v_k_980_);
v___x_987_ = lean_uint64_dec_eq(v_k_979_, v___x_986_);
if (v___x_987_ == 0)
{
v_t_978_ = v_r_983_;
goto _start;
}
else
{
lean_object* v___x_989_; 
lean_inc(v_v_981_);
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v_v_981_);
return v___x_989_;
}
}
else
{
v_t_978_ = v_l_982_;
goto _start;
}
}
else
{
lean_object* v___x_991_; 
v___x_991_ = lean_box(0);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_992_, lean_object* v_k_993_){
_start:
{
uint64_t v_k_boxed_994_; lean_object* v_res_995_; 
v_k_boxed_994_ = lean_unbox_uint64(v_k_993_);
lean_dec_ref(v_k_993_);
v_res_995_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_t_992_, v_k_boxed_994_);
lean_dec(v_t_992_);
return v_res_995_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v_stx_1008_, uint8_t v_builtin_1009_, lean_object* v_decl_1010_, lean_object* v___x_1011_, lean_object* v___x_1012_, uint8_t v___x_1013_, uint8_t v_kind_1014_, lean_object* v_name_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___x_1122_; 
lean_inc_ref(v___y_1018_);
v___x_1122_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1008_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1122_) == 0)
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
lean_dec_ref(v___x_1122_);
v___x_1123_ = 0;
v___x_1124_ = l_Lean_instBEqAttributeKind_beq(v_kind_1014_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
v___x_1125_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_1015_, v_kind_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v___x_1125_;
}
else
{
lean_dec(v_name_1015_);
v___y_1081_ = v___y_1016_;
v___y_1082_ = v___y_1017_;
v___y_1083_ = v___y_1018_;
v___y_1084_ = v___y_1019_;
goto v___jp_1080_;
}
}
else
{
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v_name_1015_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
return v___x_1122_;
}
v___jp_1021_:
{
lean_object* v___x_1029_; 
lean_dec_ref(v___y_1025_);
v___x_1029_ = lean_st_ref_get(v___y_1028_);
if (v_builtin_1009_ == 0)
{
lean_object* v_env_1030_; uint64_t v_javascriptHash_1031_; lean_object* v___x_1032_; lean_object* v_toEnvExtension_1033_; lean_object* v_asyncMode_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1023_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_env_1030_);
lean_dec(v___x_1029_);
v_javascriptHash_1031_ = lean_ctor_get_uint64(v___y_1022_, sizeof(void*)*1);
lean_dec_ref(v___y_1022_);
v___x_1032_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_toEnvExtension_1033_);
v_asyncMode_1034_ = lean_ctor_get(v_toEnvExtension_1033_, 2);
lean_inc(v_asyncMode_1034_);
lean_dec_ref(v_toEnvExtension_1033_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_decl_1010_);
lean_ctor_set(v___x_1035_, 1, v___y_1024_);
v___x_1036_ = lean_box_uint64(v_javascriptHash_1031_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1032_, v_env_1030_, v___x_1037_, v_asyncMode_1034_, v___x_1038_);
lean_dec(v_asyncMode_1034_);
v___x_1040_ = l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(v___x_1039_, v___y_1026_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec(v___y_1026_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v___x_1029_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1022_);
lean_inc(v___y_1023_);
lean_inc(v_decl_1010_);
v___x_1041_ = l_Lean_mkConst(v_decl_1010_, v___y_1023_);
v___x_1042_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1043_ = l_Lean_Name_mkStr3(v___x_1011_, v___x_1012_, v___x_1042_);
v___x_1044_ = l_Lean_mkConst(v___x_1043_, v___y_1023_);
lean_inc(v_decl_1010_);
v___x_1045_ = l_Lean_instToExprName___private__1(v_decl_1010_);
v___x_1046_ = l_Lean_mkAppB(v___x_1044_, v___x_1045_, v___x_1041_);
v___x_1047_ = l_Lean_declareBuiltin(v_decl_1010_, v___x_1046_, v___y_1027_, v___y_1028_);
return v___x_1047_;
}
}
v___jp_1048_:
{
lean_object* v___x_1057_; lean_object* v_toEnvExtension_1058_; lean_object* v_asyncMode_1059_; uint64_t v_javascriptHash_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1057_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_toEnvExtension_1058_);
v_asyncMode_1059_ = lean_ctor_get(v_toEnvExtension_1058_, 2);
lean_inc(v_asyncMode_1059_);
lean_dec_ref(v_toEnvExtension_1058_);
v_javascriptHash_1060_ = lean_ctor_get_uint64(v___y_1049_, sizeof(void*)*1);
v___x_1061_ = lean_box(1);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1061_, v___x_1057_, v___y_1052_, v_asyncMode_1059_, v___x_1062_);
lean_dec(v_asyncMode_1059_);
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1063_, v_javascriptHash_1060_);
lean_dec(v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 1)
{
lean_object* v_val_1065_; lean_object* v_fst_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1078_; 
v_val_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref(v___x_1064_);
v_fst_1066_ = lean_ctor_get(v_val_1065_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_val_1065_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_val_1065_, 1);
lean_dec(v_unused_1079_);
v___x_1068_ = v_val_1065_;
v_isShared_1069_ = v_isSharedCheck_1078_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_fst_1066_);
lean_dec(v_val_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1078_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1070_ = lean_obj_once(&l_Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1071_ = l_Lean_MessageData_ofConstName(v_fst_1066_, v___x_1013_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 7);
lean_ctor_set(v___x_1068_, 1, v___x_1071_);
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l_Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc_ref(v___y_1055_);
v___x_1076_ = l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(v___x_1075_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_dec_ref(v___x_1076_);
v___y_1022_ = v___y_1049_;
v___y_1023_ = v___y_1050_;
v___y_1024_ = v___y_1051_;
v___y_1025_ = v___y_1053_;
v___y_1026_ = v___y_1054_;
v___y_1027_ = v___y_1055_;
v___y_1028_ = v___y_1056_;
goto v___jp_1021_;
}
else
{
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
return v___x_1076_;
}
}
}
}
else
{
lean_dec(v___x_1064_);
v___y_1022_ = v___y_1049_;
v___y_1023_ = v___y_1050_;
v___y_1024_ = v___y_1051_;
v___y_1025_ = v___y_1053_;
v___y_1026_ = v___y_1054_;
v___y_1027_ = v___y_1055_;
v___y_1028_ = v___y_1056_;
goto v___jp_1021_;
}
}
v___jp_1080_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1085_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1086_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
lean_inc_ref(v___x_1012_);
lean_inc_ref(v___x_1011_);
v___x_1087_ = l_Lean_Name_mkStr4(v___x_1011_, v___x_1012_, v___x_1085_, v___x_1086_);
v___x_1088_ = lean_box(0);
lean_inc(v_decl_1010_);
v___x_1089_ = l_Lean_Expr_const___override(v_decl_1010_, v___x_1088_);
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_mk_empty_array_with_capacity(v___x_1090_);
v___x_1092_ = lean_array_push(v___x_1091_, v___x_1089_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
v___x_1093_ = l_Lean_Meta_mkAppM(v___x_1087_, v___x_1092_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v_a_1094_);
v___x_1095_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_1094_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1084_);
if (v_builtin_1009_ == 0)
{
lean_object* v_env_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint64_t v_javascriptHash_1101_; lean_object* v___x_1102_; 
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1098_);
lean_dec(v___x_1097_);
v___x_1099_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1100_ = lean_st_ref_get(v___x_1099_);
v_javascriptHash_1101_ = lean_ctor_get_uint64(v_a_1096_, sizeof(void*)*1);
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1100_, v_javascriptHash_1101_);
lean_dec(v___x_1100_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v___x_1102_);
v___x_1103_ = lean_obj_once(&l_Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
lean_inc_ref(v___y_1083_);
v___x_1104_ = l_Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(v___x_1103_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref(v___x_1104_);
v___y_1049_ = v_a_1096_;
v___y_1050_ = v___x_1088_;
v___y_1051_ = v_a_1094_;
v___y_1052_ = v_env_1098_;
v___y_1053_ = v___y_1081_;
v___y_1054_ = v___y_1082_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___y_1084_;
goto v___jp_1048_;
}
else
{
lean_dec_ref(v_env_1098_);
lean_dec(v_a_1096_);
lean_dec(v_a_1094_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
return v___x_1104_;
}
}
else
{
lean_dec(v___x_1102_);
v___y_1049_ = v_a_1096_;
v___y_1050_ = v___x_1088_;
v___y_1051_ = v_a_1094_;
v___y_1052_ = v_env_1098_;
v___y_1053_ = v___y_1081_;
v___y_1054_ = v___y_1082_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___y_1084_;
goto v___jp_1048_;
}
}
else
{
lean_object* v_env_1105_; 
v_env_1105_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1097_);
v___y_1049_ = v_a_1096_;
v___y_1050_ = v___x_1088_;
v___y_1051_ = v_a_1094_;
v___y_1052_ = v_env_1105_;
v___y_1053_ = v___y_1081_;
v___y_1054_ = v___y_1082_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___y_1084_;
goto v___jp_1048_;
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v_a_1094_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
v_a_1106_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1095_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1095_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
v_a_1114_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1093_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1093_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_stx_1126_, lean_object* v_builtin_1127_, lean_object* v_decl_1128_, lean_object* v___x_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v_kind_1132_, lean_object* v_name_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v_builtin_boxed_1139_; uint8_t v___x_12119__boxed_1140_; uint8_t v_kind_boxed_1141_; lean_object* v_res_1142_; 
v_builtin_boxed_1139_ = lean_unbox(v_builtin_1127_);
v___x_12119__boxed_1140_ = lean_unbox(v___x_1131_);
v_kind_boxed_1141_ = lean_unbox(v_kind_1132_);
v_res_1142_ = l_Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v_stx_1126_, v_builtin_boxed_1139_, v_decl_1128_, v___x_1129_, v___x_1130_, v___x_12119__boxed_1140_, v_kind_boxed_1141_, v_name_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object* v___y_1143_, uint8_t v_isExporting_1144_, lean_object* v___x_1145_, lean_object* v___y_1146_, lean_object* v___x_1147_, lean_object* v_a_x3f_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_env_1151_; lean_object* v_nextMacroScope_1152_; lean_object* v_ngen_1153_; lean_object* v_auxDeclNGen_1154_; lean_object* v_traceState_1155_; lean_object* v_messages_1156_; lean_object* v_infoState_1157_; lean_object* v_snapshotTasks_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1183_; 
v___x_1150_ = lean_st_ref_take(v___y_1143_);
v_env_1151_ = lean_ctor_get(v___x_1150_, 0);
v_nextMacroScope_1152_ = lean_ctor_get(v___x_1150_, 1);
v_ngen_1153_ = lean_ctor_get(v___x_1150_, 2);
v_auxDeclNGen_1154_ = lean_ctor_get(v___x_1150_, 3);
v_traceState_1155_ = lean_ctor_get(v___x_1150_, 4);
v_messages_1156_ = lean_ctor_get(v___x_1150_, 6);
v_infoState_1157_ = lean_ctor_get(v___x_1150_, 7);
v_snapshotTasks_1158_ = lean_ctor_get(v___x_1150_, 8);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v___x_1150_, 5);
lean_dec(v_unused_1184_);
v___x_1160_ = v___x_1150_;
v_isShared_1161_ = v_isSharedCheck_1183_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snapshotTasks_1158_);
lean_inc(v_infoState_1157_);
lean_inc(v_messages_1156_);
lean_inc(v_traceState_1155_);
lean_inc(v_auxDeclNGen_1154_);
lean_inc(v_ngen_1153_);
lean_inc(v_nextMacroScope_1152_);
lean_inc(v_env_1151_);
lean_dec(v___x_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1183_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_Environment_setExporting(v_env_1151_, v_isExporting_1144_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 5, v___x_1145_);
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_nextMacroScope_1152_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_ngen_1153_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_auxDeclNGen_1154_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v_traceState_1155_);
lean_ctor_set(v_reuseFailAlloc_1182_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1182_, 6, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1182_, 7, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1182_, 8, v_snapshotTasks_1158_);
v___x_1164_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_mctx_1167_; lean_object* v_zetaDeltaFVarIds_1168_; lean_object* v_postponed_1169_; lean_object* v_diag_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v___x_1165_ = lean_st_ref_set(v___y_1143_, v___x_1164_);
v___x_1166_ = lean_st_ref_take(v___y_1146_);
v_mctx_1167_ = lean_ctor_get(v___x_1166_, 0);
v_zetaDeltaFVarIds_1168_ = lean_ctor_get(v___x_1166_, 2);
v_postponed_1169_ = lean_ctor_get(v___x_1166_, 3);
v_diag_1170_ = lean_ctor_get(v___x_1166_, 4);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1166_, 1);
lean_dec(v_unused_1181_);
v___x_1172_ = v___x_1166_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_diag_1170_);
lean_inc(v_postponed_1169_);
lean_inc(v_zetaDeltaFVarIds_1168_);
lean_inc(v_mctx_1167_);
lean_dec(v___x_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1147_);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_mctx_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_zetaDeltaFVarIds_1168_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_postponed_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_diag_1170_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_st_ref_set(v___y_1146_, v___x_1175_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object* v___y_1185_, lean_object* v_isExporting_1186_, lean_object* v___x_1187_, lean_object* v___y_1188_, lean_object* v___x_1189_, lean_object* v_a_x3f_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_isExporting_boxed_1192_; lean_object* v_res_1193_; 
v_isExporting_boxed_1192_ = lean_unbox(v_isExporting_1186_);
v_res_1193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1185_, v_isExporting_boxed_1192_, v___x_1187_, v___y_1188_, v___x_1189_, v_a_x3f_1190_);
lean_dec(v_a_x3f_1190_);
lean_dec(v___y_1188_);
lean_dec(v___y_1185_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object* v_x_1194_, uint8_t v_isExporting_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_env_1202_; uint8_t v_isExporting_1203_; lean_object* v___x_1204_; lean_object* v_env_1205_; lean_object* v_nextMacroScope_1206_; lean_object* v_ngen_1207_; lean_object* v_auxDeclNGen_1208_; lean_object* v_traceState_1209_; lean_object* v_messages_1210_; lean_object* v_infoState_1211_; lean_object* v_snapshotTasks_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1266_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v_isExporting_1203_ = lean_ctor_get_uint8(v_env_1202_, sizeof(void*)*8);
lean_dec_ref(v_env_1202_);
v___x_1204_ = lean_st_ref_take(v___y_1199_);
v_env_1205_ = lean_ctor_get(v___x_1204_, 0);
v_nextMacroScope_1206_ = lean_ctor_get(v___x_1204_, 1);
v_ngen_1207_ = lean_ctor_get(v___x_1204_, 2);
v_auxDeclNGen_1208_ = lean_ctor_get(v___x_1204_, 3);
v_traceState_1209_ = lean_ctor_get(v___x_1204_, 4);
v_messages_1210_ = lean_ctor_get(v___x_1204_, 6);
v_infoState_1211_ = lean_ctor_get(v___x_1204_, 7);
v_snapshotTasks_1212_ = lean_ctor_get(v___x_1204_, 8);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1204_, 5);
lean_dec(v_unused_1267_);
v___x_1214_ = v___x_1204_;
v_isShared_1215_ = v_isSharedCheck_1266_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snapshotTasks_1212_);
lean_inc(v_infoState_1211_);
lean_inc(v_messages_1210_);
lean_inc(v_traceState_1209_);
lean_inc(v_auxDeclNGen_1208_);
lean_inc(v_ngen_1207_);
lean_inc(v_nextMacroScope_1206_);
lean_inc(v_env_1205_);
lean_dec(v___x_1204_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1266_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = l_Lean_Environment_setExporting(v_env_1205_, v_isExporting_1195_);
v___x_1217_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 5, v___x_1217_);
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_nextMacroScope_1206_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_ngen_1207_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_auxDeclNGen_1208_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_traceState_1209_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_messages_1210_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_infoState_1211_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_snapshotTasks_1212_);
v___x_1219_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_mctx_1222_; lean_object* v_zetaDeltaFVarIds_1223_; lean_object* v_postponed_1224_; lean_object* v_diag_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1263_; 
v___x_1220_ = lean_st_ref_set(v___y_1199_, v___x_1219_);
v___x_1221_ = lean_st_ref_take(v___y_1197_);
v_mctx_1222_ = lean_ctor_get(v___x_1221_, 0);
v_zetaDeltaFVarIds_1223_ = lean_ctor_get(v___x_1221_, 2);
v_postponed_1224_ = lean_ctor_get(v___x_1221_, 3);
v_diag_1225_ = lean_ctor_get(v___x_1221_, 4);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1221_, 1);
lean_dec(v_unused_1264_);
v___x_1227_ = v___x_1221_;
v_isShared_1228_ = v_isSharedCheck_1263_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_diag_1225_);
lean_inc(v_postponed_1224_);
lean_inc(v_zetaDeltaFVarIds_1223_);
lean_inc(v_mctx_1222_);
lean_dec(v___x_1221_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1263_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_mctx_1222_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_zetaDeltaFVarIds_1223_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_postponed_1224_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_diag_1225_);
v___x_1231_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v_r_1233_; 
v___x_1232_ = lean_st_ref_set(v___y_1197_, v___x_1231_);
lean_inc(v___y_1199_);
lean_inc(v___y_1197_);
v_r_1233_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
if (lean_obj_tag(v_r_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1250_; 
v_a_1234_ = lean_ctor_get(v_r_1233_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_r_1233_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1236_ = v_r_1233_;
v_isShared_1237_ = v_isSharedCheck_1250_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v_r_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1250_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
lean_inc(v_a_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set_tag(v___x_1236_, 1);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v___x_1240_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1199_, v_isExporting_1203_, v___x_1217_, v___y_1197_, v___x_1229_, v___x_1239_);
lean_dec_ref(v___x_1239_);
lean_dec(v___y_1197_);
lean_dec(v___y_1199_);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1240_, 0);
lean_dec(v_unused_1248_);
v___x_1242_ = v___x_1240_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v___x_1240_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_a_1234_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1234_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_a_1251_ = lean_ctor_get(v_r_1233_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v_r_1233_);
v___x_1252_ = lean_box(0);
v___x_1253_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1199_, v_isExporting_1203_, v___x_1217_, v___y_1197_, v___x_1229_, v___x_1252_);
lean_dec(v___y_1197_);
lean_dec(v___y_1199_);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v___x_1253_, 0);
lean_dec(v_unused_1261_);
v___x_1255_ = v___x_1253_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v___x_1253_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
lean_ctor_set(v___x_1255_, 0, v_a_1251_);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1251_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object* v_x_1268_, lean_object* v_isExporting_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v_isExporting_boxed_1275_; lean_object* v_res_1276_; 
v_isExporting_boxed_1275_ = lean_unbox(v_isExporting_1269_);
v_res_1276_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1268_, v_isExporting_boxed_1275_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(lean_object* v_x_1277_, uint8_t v_when_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
if (v_when_1278_ == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_apply_5(v_x_1277_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, lean_box(0));
return v___x_1284_;
}
else
{
uint8_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = 0;
v___x_1286_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1277_, v___x_1285_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_x_1287_, lean_object* v_when_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v_when_boxed_1294_; lean_object* v_res_1295_; 
v_when_boxed_1294_ = lean_unbox(v_when_1288_);
v_res_1295_ = l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v_x_1287_, v_when_boxed_1294_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = lean_box(1);
v___x_1300_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1301_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v___x_1299_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
lean_ctor_set(v___x_1307_, 2, v___x_1306_);
lean_ctor_set(v___x_1307_, 3, v___x_1305_);
lean_ctor_set(v___x_1307_, 4, v___x_1305_);
lean_ctor_set(v___x_1307_, 5, v___x_1305_);
lean_ctor_set(v___x_1307_, 6, v___x_1305_);
lean_ctor_set(v___x_1307_, 7, v___x_1305_);
lean_ctor_set(v___x_1307_, 8, v___x_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
lean_ctor_set(v___x_1309_, 3, v___x_1308_);
lean_ctor_set(v___x_1309_, 4, v___x_1308_);
lean_ctor_set(v___x_1309_, 5, v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
lean_ctor_set(v___x_1311_, 2, v___x_1310_);
lean_ctor_set(v___x_1311_, 3, v___x_1310_);
lean_ctor_set(v___x_1311_, 4, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v___x_1312_, uint8_t v___x_1313_, uint8_t v_builtin_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, lean_object* v_name_1317_, lean_object* v_decl_1318_, lean_object* v_stx_1319_, uint8_t v_kind_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___f_1340_; lean_object* v___x_1341_; 
v___x_1324_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_1325_ = 0;
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1328_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1329_ = ((lean_object*)(l_Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1330_ = lean_box(0);
lean_inc(v___x_1312_);
v___x_1331_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1331_, 0, v___x_1324_);
lean_ctor_set(v___x_1331_, 1, v___x_1312_);
lean_ctor_set(v___x_1331_, 2, v___x_1328_);
lean_ctor_set(v___x_1331_, 3, v___x_1329_);
lean_ctor_set(v___x_1331_, 4, v___x_1330_);
lean_ctor_set(v___x_1331_, 5, v___x_1326_);
lean_ctor_set(v___x_1331_, 6, v___x_1330_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7, v___x_1325_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7 + 1, v___x_1325_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7 + 2, v___x_1325_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7 + 3, v___x_1313_);
v___x_1332_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1333_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1334_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1332_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1312_);
lean_ctor_set(v___x_1335_, 3, v___x_1327_);
lean_ctor_set(v___x_1335_, 4, v___x_1334_);
v___x_1336_ = lean_st_mk_ref(v___x_1335_);
v___x_1337_ = lean_box(v_builtin_1314_);
v___x_1338_ = lean_box(v___x_1313_);
v___x_1339_ = lean_box(v_kind_1320_);
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 13, 8);
lean_closure_set(v___f_1340_, 0, v_stx_1319_);
lean_closure_set(v___f_1340_, 1, v___x_1337_);
lean_closure_set(v___f_1340_, 2, v_decl_1318_);
lean_closure_set(v___f_1340_, 3, v___x_1315_);
lean_closure_set(v___f_1340_, 4, v___x_1316_);
lean_closure_set(v___f_1340_, 5, v___x_1338_);
lean_closure_set(v___f_1340_, 6, v___x_1339_);
lean_closure_set(v___f_1340_, 7, v_name_1317_);
lean_inc(v___x_1336_);
v___x_1341_ = l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v___f_1340_, v___x_1313_, v___x_1331_, v___x_1336_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_st_ref_get(v___x_1336_);
lean_dec(v___x_1336_);
lean_dec(v___x_1346_);
if (v_isShared_1345_ == 0)
{
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1342_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_dec(v___x_1336_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v___x_1351_, lean_object* v___x_1352_, lean_object* v_builtin_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v_name_1356_, lean_object* v_decl_1357_, lean_object* v_stx_1358_, lean_object* v_kind_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v___x_12648__boxed_1363_; uint8_t v_builtin_boxed_1364_; uint8_t v_kind_boxed_1365_; lean_object* v_res_1366_; 
v___x_12648__boxed_1363_ = lean_unbox(v___x_1352_);
v_builtin_boxed_1364_ = lean_unbox(v_builtin_1353_);
v_kind_boxed_1365_ = lean_unbox(v_kind_1359_);
v_res_1366_ = l_Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1351_, v___x_12648__boxed_1363_, v_builtin_boxed_1364_, v___x_1354_, v___x_1355_, v_name_1356_, v_decl_1357_, v_stx_1358_, v_kind_boxed_1365_, v___y_1360_, v___y_1361_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v___x_1374_, uint8_t v_builtin_1375_, lean_object* v_name_1376_){
_start:
{
lean_object* v___f_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___f_1385_; lean_object* v___y_1387_; 
lean_inc(v_name_1376_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1378_, 0, v_name_1376_);
v___x_1379_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0));
v___x_1380_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1));
v___x_1381_ = ((lean_object*)(l_Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1382_ = 1;
v___x_1383_ = lean_box(v___x_1382_);
v___x_1384_ = lean_box(v_builtin_1375_);
lean_inc(v_name_1376_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1385_, 0, v___x_1374_);
lean_closure_set(v___f_1385_, 1, v___x_1383_);
lean_closure_set(v___f_1385_, 2, v___x_1384_);
lean_closure_set(v___f_1385_, 3, v___x_1379_);
lean_closure_set(v___f_1385_, 4, v___x_1380_);
lean_closure_set(v___f_1385_, 5, v_name_1376_);
if (v_builtin_1375_ == 0)
{
lean_object* v___x_1410_; 
v___x_1410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___y_1387_ = v___x_1410_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1411_; 
v___x_1411_ = ((lean_object*)(l_Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___y_1387_ = v___x_1411_;
goto v___jp_1386_;
}
v___jp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v_impl_1392_; lean_object* v___x_1393_; 
v___x_1388_ = ((lean_object*)(l_Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1389_ = lean_string_append(v___y_1387_, v___x_1388_);
v___x_1390_ = 1;
v___x_1391_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1391_, 0, v___x_1381_);
lean_ctor_set(v___x_1391_, 1, v_name_1376_);
lean_ctor_set(v___x_1391_, 2, v___x_1389_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*3, v___x_1390_);
v_impl_1392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_impl_1392_, 0, v___x_1391_);
lean_ctor_set(v_impl_1392_, 1, v___f_1385_);
lean_ctor_set(v_impl_1392_, 2, v___f_1378_);
lean_inc_ref(v_impl_1392_);
v___x_1393_ = l_Lean_registerBuiltinAttribute(v_impl_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1401_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_impl_1392_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_impl_1392_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v_impl_1392_);
v_a_1402_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1393_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1393_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v___x_1412_, lean_object* v_builtin_1413_, lean_object* v_name_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v_builtin_boxed_1416_; lean_object* v_res_1417_; 
v_builtin_boxed_1416_ = lean_unbox(v_builtin_1413_);
v_res_1417_ = l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1412_, v_builtin_boxed_1416_, v_name_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1425_ = lean_box(1);
v___x_1426_ = 1;
v___x_1427_ = ((lean_object*)(l_Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1428_ = l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1425_, v___x_1426_, v___x_1427_);
if (lean_obj_tag(v___x_1428_) == 0)
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v___x_1428_);
v___x_1429_ = 0;
v___x_1430_ = ((lean_object*)(l_Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1431_ = l_Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1425_, v___x_1429_, v___x_1430_);
return v___x_1431_;
}
else
{
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v_msg_1435_, v___y_1436_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(v_00_u03b1_1440_, v_msg_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_1446_, lean_object* v_t_1447_, uint64_t v_k_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_t_1447_, v_k_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_1450_, lean_object* v_t_1451_, lean_object* v_k_1452_){
_start:
{
uint64_t v_k_boxed_1453_; lean_object* v_res_1454_; 
v_k_boxed_1453_ = lean_unbox_uint64(v_k_1452_);
lean_dec_ref(v_k_1452_);
v_res_1454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(v_00_u03b4_1450_, v_t_1451_, v_k_boxed_1453_);
lean_dec(v_t_1451_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1455_, lean_object* v_name_1456_, uint8_t v_kind_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_1456_, v_kind_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_name_1465_, lean_object* v_kind_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v_kind_boxed_1472_; lean_object* v_res_1473_; 
v_kind_boxed_1472_ = lean_unbox(v_kind_1466_);
v_res_1473_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(v_00_u03b1_1464_, v_name_1465_, v_kind_boxed_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(lean_object* v_00_u03b1_1474_, lean_object* v_x_1475_, uint8_t v_isExporting_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1475_, v_isExporting_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_x_1484_, lean_object* v_isExporting_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_isExporting_boxed_1491_; lean_object* v_res_1492_; 
v_isExporting_boxed_1491_ = lean_unbox(v_isExporting_1485_);
v_res_1492_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(v_00_u03b1_1483_, v_x_1484_, v_isExporting_boxed_1491_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1493_, lean_object* v_x_1494_, uint8_t v_when_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v_x_1494_, v_when_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_x_1503_, lean_object* v_when_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v_when_boxed_1510_; lean_object* v_res_1511_; 
v_when_boxed_1510_ = lean_unbox(v_when_1504_);
v_res_1511_ = l_Lean_withoutExporting___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(v_00_u03b1_1502_, v_x_1503_, v_when_boxed_1510_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1512_, lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1520_, v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
if (lean_obj_tag(v_a_1528_) == 0)
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_array_to_list(v_a_1529_);
return v___x_1530_;
}
else
{
lean_object* v_head_1531_; lean_object* v_tail_1532_; lean_object* v___x_1533_; 
v_head_1531_ = lean_ctor_get(v_a_1528_, 0);
lean_inc(v_head_1531_);
v_tail_1532_ = lean_ctor_get(v_a_1528_, 1);
lean_inc(v_tail_1532_);
lean_dec_ref(v_a_1528_);
v___x_1533_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1529_, v_head_1531_);
v_a_1528_ = v_tail_1532_;
v_a_1529_ = v___x_1533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object* v_x_1539_){
_start:
{
uint64_t v_hash_1540_; lean_object* v_pos_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_hash_1540_ = lean_ctor_get_uint64(v_x_1539_, sizeof(void*)*1);
v_pos_1541_ = lean_ctor_get(v_x_1539_, 0);
lean_inc_ref(v_pos_1541_);
lean_dec_ref(v_x_1539_);
v___x_1542_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
v___x_1543_ = lean_uint64_to_nat(v_hash_1540_);
v___x_1544_ = l_Lean_bignumToJson(v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1542_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1549_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_1541_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1546_);
v___x_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___x_1546_);
v___x_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1547_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1555_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1553_, v___x_1554_);
v___x_1556_ = l_Lean_Json_mkObj(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object* v_j_1559_, lean_object* v_k_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = l_Lean_Json_getObjValD(v_j_1559_, v_k_1560_);
v___x_1562_ = l_UInt64_fromJson_x3f(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object* v_j_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_j_1563_, v_k_1564_);
lean_dec_ref(v_k_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object* v_j_1566_, lean_object* v_k_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = l_Lean_Json_getObjValD(v_j_1566_, v_k_1567_);
v___x_1569_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object* v_j_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_j_1570_, v_k_1571_);
lean_dec_ref(v_k_1571_);
return v_res_1572_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = 1;
v___x_1579_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1));
v___x_1580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1579_, v___x_1578_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1582_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2);
v___x_1583_ = lean_string_append(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = 1;
v___x_1587_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4));
v___x_1588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1587_, v___x_1586_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5);
v___x_1590_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1594_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6);
v___x_1595_ = lean_string_append(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = 1;
v___x_1599_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9));
v___x_1600_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1599_, v___x_1598_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10);
v___x_1602_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1603_ = lean_string_append(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1605_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11);
v___x_1606_ = lean_string_append(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object* v_json_1607_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
lean_inc(v_json_1607_);
v___x_1609_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_json_1607_, v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_json_1607_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1614_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8);
v___x_1615_ = lean_string_append(v___x_1614_, v_a_1610_);
lean_dec(v_a_1610_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_json_1607_);
v_a_1620_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1609_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1609_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_a_1628_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1609_);
v___x_1629_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1630_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_json_1607_, v___x_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1628_);
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1635_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12);
v___x_1636_ = lean_string_append(v___x_1635_, v_a_1631_);
lean_dec(v_a_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1636_);
v___x_1638_ = v___x_1633_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
else
{
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1628_);
v_a_1641_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1630_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1630_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 0);
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1658_; 
v_a_1649_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1651_ = v___x_1630_;
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1630_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; uint64_t v___x_1654_; lean_object* v___x_1656_; 
v___x_1653_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1653_, 0, v_a_1649_);
v___x_1654_ = lean_unbox_uint64(v_a_1628_);
lean_dec(v_a_1628_);
lean_ctor_set_uint64(v___x_1653_, sizeof(void*)*1, v___x_1654_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1653_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson(lean_object* v_x_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1665_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_x_1664_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___x_1668_);
v___x_1671_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1672_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1670_, v___x_1671_);
v___x_1673_ = l_Lean_Json_mkObj(v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(lean_object* v_j_1676_, lean_object* v_k_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = l_Lean_Json_getObjValD(v_j_1676_, v_k_1677_);
v___x_1679_ = l_Lean_Json_getStr_x3f(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0___boxed(lean_object* v_j_1680_, lean_object* v_k_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_j_1680_, v_k_1681_);
lean_dec_ref(v_k_1681_);
return v_res_1682_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = 1;
v___x_1689_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1));
v___x_1690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1692_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2);
v___x_1693_ = lean_string_append(v___x_1692_, v___x_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = 1;
v___x_1697_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4));
v___x_1698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1697_, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5);
v___x_1700_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3);
v___x_1701_ = lean_string_append(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1703_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6);
v___x_1704_ = lean_string_append(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson(lean_object* v_json_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1707_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_1705_, v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1717_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7);
v___x_1713_ = lean_string_append(v___x_1712_, v_a_1708_);
lean_dec(v_a_1708_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1707_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1707_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 0);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1726_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1707_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1707_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object* v___y_1736_){
_start:
{
lean_object* v_doc_1738_; lean_object* v___x_1739_; 
v_doc_1738_ = lean_ctor_get(v___y_1736_, 1);
lean_inc_ref(v_doc_1738_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_doc_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1740_);
lean_dec_ref(v___y_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t v_k_1743_, lean_object* v_t_1744_){
_start:
{
if (lean_obj_tag(v_t_1744_) == 0)
{
lean_object* v_k_1745_; lean_object* v_l_1746_; lean_object* v_r_1747_; uint64_t v___x_1748_; uint8_t v___x_1749_; 
v_k_1745_ = lean_ctor_get(v_t_1744_, 1);
v_l_1746_ = lean_ctor_get(v_t_1744_, 3);
v_r_1747_ = lean_ctor_get(v_t_1744_, 4);
v___x_1748_ = lean_unbox_uint64(v_k_1745_);
v___x_1749_ = lean_uint64_dec_lt(v_k_1743_, v___x_1748_);
if (v___x_1749_ == 0)
{
uint64_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_unbox_uint64(v_k_1745_);
v___x_1751_ = lean_uint64_dec_eq(v_k_1743_, v___x_1750_);
if (v___x_1751_ == 0)
{
v_t_1744_ = v_r_1747_;
goto _start;
}
else
{
return v___x_1751_;
}
}
else
{
v_t_1744_ = v_l_1746_;
goto _start;
}
}
else
{
uint8_t v___x_1754_; 
v___x_1754_ = 0;
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object* v_k_1755_, lean_object* v_t_1756_){
_start:
{
uint64_t v_k_boxed_1757_; uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_k_boxed_1757_ = lean_unbox_uint64(v_k_1755_);
lean_dec_ref(v_k_1755_);
v_res_1758_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_boxed_1757_, v_t_1756_);
lean_dec(v_t_1756_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object* v___x_1760_, uint64_t v_hash_1761_, lean_object* v_s_1762_){
_start:
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1762_);
v___x_1764_ = lean_nat_dec_le(v___x_1760_, v___x_1763_);
lean_dec(v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v_toEnvExtension_1766_; lean_object* v_asyncMode_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1765_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_ref(v_toEnvExtension_1766_);
v_asyncMode_1767_ = lean_ctor_get(v_toEnvExtension_1766_, 2);
lean_inc(v_asyncMode_1767_);
lean_dec_ref(v_toEnvExtension_1766_);
v___x_1768_ = lean_box(1);
v___x_1769_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_1762_);
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1768_, v___x_1765_, v___x_1769_, v_asyncMode_1767_, v___x_1770_);
lean_dec(v_asyncMode_1767_);
v___x_1772_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_hash_1761_, v___x_1771_);
lean_dec(v___x_1771_);
return v___x_1772_;
}
else
{
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object* v___x_1773_, lean_object* v_hash_1774_, lean_object* v_s_1775_){
_start:
{
uint64_t v_hash_boxed_1776_; uint8_t v_res_1777_; lean_object* v_r_1778_; 
v_hash_boxed_1776_ = lean_unbox_uint64(v_hash_1774_);
lean_dec_ref(v_hash_1774_);
v_res_1777_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1773_, v_hash_boxed_1776_, v_s_1775_);
lean_dec_ref(v_s_1775_);
lean_dec(v___x_1773_);
v_r_1778_ = lean_box(v_res_1777_);
return v_r_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object* v___x_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1779_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object* v___x_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1783_, v___y_1784_);
lean_dec_ref(v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object* v_snd_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_snd_1787_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1806_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1806_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1806_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_javascript_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v_javascript_1801_ = lean_ctor_get(v_a_1797_, 0);
lean_inc_ref(v_javascript_1801_);
lean_dec(v_a_1797_);
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_javascript_1801_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_a_1807_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1796_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1796_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object* v_snd_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t v_hash_1825_, lean_object* v___x_1826_, lean_object* v_snap_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v_toEnvExtension_1831_; lean_object* v_asyncMode_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1830_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc_ref(v_toEnvExtension_1831_);
v_asyncMode_1832_ = lean_ctor_get(v_toEnvExtension_1831_, 2);
lean_inc(v_asyncMode_1832_);
lean_dec_ref(v_toEnvExtension_1831_);
v___x_1833_ = lean_box(1);
v___x_1834_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1827_);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1833_, v___x_1830_, v___x_1834_, v_asyncMode_1832_, v___x_1835_);
lean_dec(v_asyncMode_1832_);
v___x_1837_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1836_, v_hash_1825_);
lean_dec(v___x_1836_);
if (lean_obj_tag(v___x_1837_) == 1)
{
lean_object* v_val_1838_; lean_object* v_snd_1839_; lean_object* v___f_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v___x_1826_);
v_val_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_val_1838_);
lean_dec_ref(v___x_1837_);
v_snd_1839_ = lean_ctor_get(v_val_1838_, 1);
lean_inc(v_snd_1839_);
lean_dec(v_val_1838_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__2___boxed), 9, 1);
lean_closure_set(v___f_1840_, 0, v_snd_1839_);
v___x_1841_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1827_, v___f_1840_, v___y_1828_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; 
lean_dec(v___x_1837_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v_snap_1827_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1826_);
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object* v_hash_1843_, lean_object* v___x_1844_, lean_object* v_snap_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
uint64_t v_hash_boxed_1848_; lean_object* v_res_1849_; 
v_hash_boxed_1848_ = lean_unbox_uint64(v_hash_1843_);
lean_dec_ref(v_hash_1843_);
v_res_1849_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_boxed_1848_, v___x_1844_, v_snap_1845_, v___y_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource(lean_object* v_args_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint64_t v_hash_1857_; lean_object* v_pos_1858_; lean_object* v___x_1859_; 
v___x_1855_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1856_ = lean_st_ref_get(v___x_1855_);
v_hash_1857_ = lean_ctor_get_uint64(v_args_1852_, sizeof(void*)*1);
v_pos_1858_ = lean_ctor_get(v_args_1852_, 0);
lean_inc_ref(v_pos_1858_);
lean_dec_ref(v_args_1852_);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1856_, v_hash_1857_);
lean_dec(v___x_1856_);
if (lean_obj_tag(v___x_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1871_; 
lean_dec_ref(v_pos_1858_);
lean_dec_ref(v_a_1853_);
v_val_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1871_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_val_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1871_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_snd_1864_; lean_object* v_javascript_1865_; lean_object* v___x_1867_; 
v_snd_1864_ = lean_ctor_get(v_val_1860_, 1);
lean_inc(v_snd_1864_);
lean_dec(v_val_1860_);
v_javascript_1865_ = lean_ctor_get(v_snd_1864_, 0);
lean_inc_ref(v_javascript_1865_);
lean_dec(v_snd_1864_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_javascript_1865_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_javascript_1865_);
v___x_1867_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_task_pure(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v_a_1873_; lean_object* v_toEditableDocumentCore_1874_; lean_object* v_meta_1875_; lean_object* v_text_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___f_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
lean_dec(v___x_1859_);
v___x_1872_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_1853_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v_toEditableDocumentCore_1874_ = lean_ctor_get(v_a_1873_, 0);
v_meta_1875_ = lean_ctor_get(v_toEditableDocumentCore_1874_, 0);
v_text_1876_ = lean_ctor_get(v_meta_1875_, 3);
v___x_1877_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1876_, v_pos_1858_);
v___x_1878_ = lean_box_uint64(v_hash_1857_);
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1879_, 0, v___x_1877_);
lean_closure_set(v___f_1879_, 1, v___x_1878_);
v___x_1880_ = 3;
v___x_1881_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_1882_ = lean_uint64_to_nat(v_hash_1857_);
v___x_1883_ = l_Nat_reprFast(v___x_1882_);
v___x_1884_ = lean_string_append(v___x_1881_, v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_1886_ = lean_string_append(v___x_1884_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*1, v___x_1880_);
lean_inc_ref(v___x_1887_);
v___f_1888_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1888_, 0, v___x_1887_);
v___x_1889_ = lean_box_uint64(v_hash_1857_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1890_, 0, v___x_1889_);
lean_closure_set(v___f_1890_, 1, v___x_1887_);
v___x_1891_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1873_, v___f_1879_, v___f_1888_, v___f_1890_, v_a_1853_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object* v_args_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Widget_getWidgetSource(v_args_1892_, v_a_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object* v_00_u03b2_1896_, uint64_t v_k_1897_, lean_object* v_t_1898_){
_start:
{
uint8_t v___x_1899_; 
v___x_1899_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1897_, v_t_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object* v_00_u03b2_1900_, lean_object* v_k_1901_, lean_object* v_t_1902_){
_start:
{
uint64_t v_k_boxed_1903_; uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_k_boxed_1903_ = lean_unbox_uint64(v_k_1901_);
lean_dec_ref(v_k_1901_);
v_res_1904_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(v_00_u03b2_1900_, v_k_boxed_1903_, v_t_1902_);
lean_dec(v_t_1902_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_1906_, lean_object* v_i_1907_, lean_object* v_k_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_array_get_size(v_keys_1906_);
v___x_1910_ = lean_nat_dec_lt(v_i_1907_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_dec(v_i_1907_);
return v___x_1910_;
}
else
{
lean_object* v_k_x27_1911_; uint8_t v___x_1912_; 
v_k_x27_1911_ = lean_array_fget_borrowed(v_keys_1906_, v_i_1907_);
v___x_1912_ = lean_name_eq(v_k_1908_, v_k_x27_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_nat_add(v_i_1907_, v___x_1913_);
lean_dec(v_i_1907_);
v_i_1907_ = v___x_1914_;
goto _start;
}
else
{
lean_dec(v_i_1907_);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_1916_, lean_object* v_i_1917_, lean_object* v_k_1918_){
_start:
{
uint8_t v_res_1919_; lean_object* v_r_1920_; 
v_res_1919_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1916_, v_i_1917_, v_k_1918_);
lean_dec(v_k_1918_);
lean_dec_ref(v_keys_1916_);
v_r_1920_ = lean_box(v_res_1919_);
return v_r_1920_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1921_; size_t v___x_1922_; size_t v___x_1923_; 
v___x_1921_ = ((size_t)5ULL);
v___x_1922_ = ((size_t)1ULL);
v___x_1923_ = lean_usize_shift_left(v___x_1922_, v___x_1921_);
return v___x_1923_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; 
v___x_1924_ = ((size_t)1ULL);
v___x_1925_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1926_ = lean_usize_sub(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_1927_, size_t v_x_1928_, lean_object* v_x_1929_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v_es_1930_; lean_object* v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v_j_1935_; lean_object* v___x_1936_; 
v_es_1930_ = lean_ctor_get(v_x_1927_, 0);
lean_inc_ref(v_es_1930_);
lean_dec_ref(v_x_1927_);
v___x_1931_ = lean_box(2);
v___x_1932_ = ((size_t)5ULL);
v___x_1933_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1934_ = lean_usize_land(v_x_1928_, v___x_1933_);
v_j_1935_ = lean_usize_to_nat(v___x_1934_);
v___x_1936_ = lean_array_get(v___x_1931_, v_es_1930_, v_j_1935_);
lean_dec(v_j_1935_);
lean_dec_ref(v_es_1930_);
switch(lean_obj_tag(v___x_1936_))
{
case 0:
{
lean_object* v_key_1937_; uint8_t v___x_1938_; 
v_key_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_key_1937_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = lean_name_eq(v_x_1929_, v_key_1937_);
lean_dec(v_key_1937_);
return v___x_1938_;
}
case 1:
{
lean_object* v_node_1939_; size_t v___x_1940_; 
v_node_1939_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_node_1939_);
lean_dec_ref(v___x_1936_);
v___x_1940_ = lean_usize_shift_right(v_x_1928_, v___x_1932_);
v_x_1927_ = v_node_1939_;
v_x_1928_ = v___x_1940_;
goto _start;
}
default: 
{
uint8_t v___x_1942_; 
v___x_1942_ = 0;
return v___x_1942_;
}
}
}
else
{
lean_object* v_ks_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_ks_1943_ = lean_ctor_get(v_x_1927_, 0);
lean_inc_ref(v_ks_1943_);
lean_dec_ref(v_x_1927_);
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_1943_, v___x_1944_, v_x_1929_);
lean_dec_ref(v_ks_1943_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_){
_start:
{
size_t v_x_1078__boxed_1949_; uint8_t v_res_1950_; lean_object* v_r_1951_; 
v_x_1078__boxed_1949_ = lean_unbox_usize(v_x_1947_);
lean_dec(v_x_1947_);
v_res_1950_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1946_, v_x_1078__boxed_1949_, v_x_1948_);
lean_dec(v_x_1948_);
v_r_1951_ = lean_box(v_res_1950_);
return v_r_1951_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1952_; uint64_t v___x_1953_; 
v___x_1952_ = lean_unsigned_to_nat(1723u);
v___x_1953_ = lean_uint64_of_nat(v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
uint64_t v___y_1957_; 
if (lean_obj_tag(v_x_1955_) == 0)
{
uint64_t v___x_1960_; 
v___x_1960_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_1957_ = v___x_1960_;
goto v___jp_1956_;
}
else
{
uint64_t v_hash_1961_; 
v_hash_1961_ = lean_ctor_get_uint64(v_x_1955_, sizeof(void*)*2);
v___y_1957_ = v_hash_1961_;
goto v___jp_1956_;
}
v___jp_1956_:
{
size_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = lean_uint64_to_usize(v___y_1957_);
v___x_1959_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1954_, v___x_1958_, v_x_1955_);
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1962_, v_x_1963_);
lean_dec(v_x_1963_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_){
_start:
{
lean_object* v_ks_1970_; lean_object* v_vs_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1995_; 
v_ks_1970_ = lean_ctor_get(v_x_1966_, 0);
v_vs_1971_ = lean_ctor_get(v_x_1966_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_x_1966_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1973_ = v_x_1966_;
v_isShared_1974_ = v_isSharedCheck_1995_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_vs_1971_);
lean_inc(v_ks_1970_);
lean_dec(v_x_1966_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1995_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = lean_array_get_size(v_ks_1970_);
v___x_1976_ = lean_nat_dec_lt(v_x_1967_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec(v_x_1967_);
v___x_1977_ = lean_array_push(v_ks_1970_, v_x_1968_);
v___x_1978_ = lean_array_push(v_vs_1971_, v_x_1969_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v___x_1978_);
lean_ctor_set(v___x_1973_, 0, v___x_1977_);
v___x_1980_ = v___x_1973_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v_k_x27_1982_; uint8_t v___x_1983_; 
v_k_x27_1982_ = lean_array_fget_borrowed(v_ks_1970_, v_x_1967_);
v___x_1983_ = lean_name_eq(v_x_1968_, v_k_x27_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1985_; 
if (v_isShared_1974_ == 0)
{
v___x_1985_ = v___x_1973_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_ks_1970_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_vs_1971_);
v___x_1985_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v_x_1967_, v___x_1986_);
lean_dec(v_x_1967_);
v_x_1966_ = v___x_1985_;
v_x_1967_ = v___x_1987_;
goto _start;
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_array_fset(v_ks_1970_, v_x_1967_, v_x_1968_);
v___x_1991_ = lean_array_fset(v_vs_1971_, v_x_1967_, v_x_1969_);
lean_dec(v_x_1967_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v___x_1991_);
lean_ctor_set(v___x_1973_, 0, v___x_1990_);
v___x_1993_ = v___x_1973_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_n_1996_, lean_object* v_k_1997_, lean_object* v_v_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_n_1996_, v___x_1999_, v_k_1997_, v_v_1998_);
return v___x_2000_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_x_2002_, size_t v_x_2003_, size_t v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 0)
{
lean_object* v_es_2007_; size_t v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; size_t v___x_2011_; lean_object* v_j_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_es_2007_ = lean_ctor_get(v_x_2002_, 0);
v___x_2008_ = ((size_t)5ULL);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2011_ = lean_usize_land(v_x_2003_, v___x_2010_);
v_j_2012_ = lean_usize_to_nat(v___x_2011_);
v___x_2013_ = lean_array_get_size(v_es_2007_);
v___x_2014_ = lean_nat_dec_lt(v_j_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_dec(v_j_2012_);
lean_dec(v_x_2006_);
lean_dec(v_x_2005_);
return v_x_2002_;
}
else
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2051_; 
lean_inc_ref(v_es_2007_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2002_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v_x_2002_, 0);
lean_dec(v_unused_2052_);
v___x_2016_ = v_x_2002_;
v_isShared_2017_ = v_isSharedCheck_2051_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v_x_2002_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2051_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v_v_2018_; lean_object* v___x_2019_; lean_object* v_xs_x27_2020_; lean_object* v___y_2022_; 
v_v_2018_ = lean_array_fget(v_es_2007_, v_j_2012_);
v___x_2019_ = lean_box(0);
v_xs_x27_2020_ = lean_array_fset(v_es_2007_, v_j_2012_, v___x_2019_);
switch(lean_obj_tag(v_v_2018_))
{
case 0:
{
lean_object* v_key_2027_; lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
v_key_2027_ = lean_ctor_get(v_v_2018_, 0);
v_val_2028_ = lean_ctor_get(v_v_2018_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_v_2018_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2030_ = v_v_2018_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_inc(v_key_2027_);
lean_dec(v_v_2018_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_name_eq(v_x_2005_, v_key_2027_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_del_object(v___x_2030_);
v___x_2033_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2027_, v_val_2028_, v_x_2005_, v_x_2006_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___y_2022_ = v___x_2034_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2036_; 
lean_dec(v_val_2028_);
lean_dec(v_key_2027_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_x_2006_);
lean_ctor_set(v___x_2030_, 0, v_x_2005_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_x_2005_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_x_2006_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v___y_2022_ = v___x_2036_;
goto v___jp_2021_;
}
}
}
}
case 1:
{
lean_object* v_node_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2049_; 
v_node_2039_ = lean_ctor_get(v_v_2018_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_v_2018_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2041_ = v_v_2018_;
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_node_2039_);
lean_dec(v_v_2018_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
size_t v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2043_ = lean_usize_shift_right(v_x_2003_, v___x_2008_);
v___x_2044_ = lean_usize_add(v_x_2004_, v___x_2009_);
v___x_2045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_node_2039_, v___x_2043_, v___x_2044_, v_x_2005_, v_x_2006_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2045_);
v___x_2047_ = v___x_2041_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v___y_2022_ = v___x_2047_;
goto v___jp_2021_;
}
}
}
default: 
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_x_2005_);
lean_ctor_set(v___x_2050_, 1, v_x_2006_);
v___y_2022_ = v___x_2050_;
goto v___jp_2021_;
}
}
v___jp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_array_fset(v_xs_x27_2020_, v_j_2012_, v___y_2022_);
lean_dec(v_j_2012_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2023_);
v___x_2025_ = v___x_2016_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
else
{
lean_object* v_ks_2053_; lean_object* v_vs_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2074_; 
v_ks_2053_ = lean_ctor_get(v_x_2002_, 0);
v_vs_2054_ = lean_ctor_get(v_x_2002_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_x_2002_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2056_ = v_x_2002_;
v_isShared_2057_ = v_isSharedCheck_2074_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_vs_2054_);
lean_inc(v_ks_2053_);
lean_dec(v_x_2002_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2074_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_ks_2053_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_vs_2054_);
v___x_2059_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v_newNode_2060_; uint8_t v___y_2062_; size_t v___x_2068_; uint8_t v___x_2069_; 
v_newNode_2060_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v___x_2059_, v_x_2005_, v_x_2006_);
v___x_2068_ = ((size_t)7ULL);
v___x_2069_ = lean_usize_dec_le(v___x_2068_, v_x_2004_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2060_);
v___x_2071_ = lean_unsigned_to_nat(4u);
v___x_2072_ = lean_nat_dec_lt(v___x_2070_, v___x_2071_);
lean_dec(v___x_2070_);
v___y_2062_ = v___x_2072_;
goto v___jp_2061_;
}
else
{
v___y_2062_ = v___x_2069_;
goto v___jp_2061_;
}
v___jp_2061_:
{
if (v___y_2062_ == 0)
{
lean_object* v_ks_2063_; lean_object* v_vs_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v_ks_2063_ = lean_ctor_get(v_newNode_2060_, 0);
lean_inc_ref(v_ks_2063_);
v_vs_2064_ = lean_ctor_get(v_newNode_2060_, 1);
lean_inc_ref(v_vs_2064_);
lean_dec_ref(v_newNode_2060_);
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0);
v___x_2067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_x_2004_, v_ks_2063_, v_vs_2064_, v___x_2065_, v___x_2066_);
lean_dec_ref(v_vs_2064_);
lean_dec_ref(v_ks_2063_);
return v___x_2067_;
}
else
{
return v_newNode_2060_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t v_depth_2075_, lean_object* v_keys_2076_, lean_object* v_vals_2077_, lean_object* v_i_2078_, lean_object* v_entries_2079_){
_start:
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_array_get_size(v_keys_2076_);
v___x_2081_ = lean_nat_dec_lt(v_i_2078_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_dec(v_i_2078_);
return v_entries_2079_;
}
else
{
lean_object* v_k_2082_; lean_object* v_v_2083_; uint64_t v___y_2085_; 
v_k_2082_ = lean_array_fget_borrowed(v_keys_2076_, v_i_2078_);
v_v_2083_ = lean_array_fget_borrowed(v_vals_2077_, v_i_2078_);
if (lean_obj_tag(v_k_2082_) == 0)
{
uint64_t v___x_2096_; 
v___x_2096_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_2085_ = v___x_2096_;
goto v___jp_2084_;
}
else
{
uint64_t v_hash_2097_; 
v_hash_2097_ = lean_ctor_get_uint64(v_k_2082_, sizeof(void*)*2);
v___y_2085_ = v_hash_2097_;
goto v___jp_2084_;
}
v___jp_2084_:
{
size_t v_h_2086_; size_t v___x_2087_; lean_object* v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v_h_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_h_2086_ = lean_uint64_to_usize(v___y_2085_);
v___x_2087_ = ((size_t)5ULL);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_sub(v_depth_2075_, v___x_2089_);
v___x_2091_ = lean_usize_mul(v___x_2087_, v___x_2090_);
v_h_2092_ = lean_usize_shift_right(v_h_2086_, v___x_2091_);
v___x_2093_ = lean_nat_add(v_i_2078_, v___x_2088_);
lean_dec(v_i_2078_);
lean_inc(v_v_2083_);
lean_inc(v_k_2082_);
v___x_2094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_entries_2079_, v_h_2092_, v_depth_2075_, v_k_2082_, v_v_2083_);
v_i_2078_ = v___x_2093_;
v_entries_2079_ = v___x_2094_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_depth_2098_, lean_object* v_keys_2099_, lean_object* v_vals_2100_, lean_object* v_i_2101_, lean_object* v_entries_2102_){
_start:
{
size_t v_depth_boxed_2103_; lean_object* v_res_2104_; 
v_depth_boxed_2103_ = lean_unbox_usize(v_depth_2098_);
lean_dec(v_depth_2098_);
v_res_2104_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_boxed_2103_, v_keys_2099_, v_vals_2100_, v_i_2101_, v_entries_2102_);
lean_dec_ref(v_vals_2100_);
lean_dec_ref(v_keys_2099_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_, lean_object* v_x_2109_){
_start:
{
size_t v_x_1234__boxed_2110_; size_t v_x_1235__boxed_2111_; lean_object* v_res_2112_; 
v_x_1234__boxed_2110_ = lean_unbox_usize(v_x_2106_);
lean_dec(v_x_2106_);
v_x_1235__boxed_2111_ = lean_unbox_usize(v_x_2107_);
lean_dec(v_x_2107_);
v_res_2112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2105_, v_x_1234__boxed_2110_, v_x_1235__boxed_2111_, v_x_2108_, v_x_2109_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_){
_start:
{
uint64_t v___y_2117_; 
if (lean_obj_tag(v_x_2114_) == 0)
{
uint64_t v___x_2121_; 
v___x_2121_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_2117_ = v___x_2121_;
goto v___jp_2116_;
}
else
{
uint64_t v_hash_2122_; 
v_hash_2122_ = lean_ctor_get_uint64(v_x_2114_, sizeof(void*)*2);
v___y_2117_ = v_hash_2122_;
goto v___jp_2116_;
}
v___jp_2116_:
{
size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_uint64_to_usize(v___y_2117_);
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2113_, v___x_2118_, v___x_2119_, v_x_2114_, v_x_2115_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v___y_2123_){
_start:
{
lean_inc(v___y_2123_);
return v___y_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(v___y_2124_);
lean_dec(v___y_2124_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object* v_expireTime_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_x_2127_);
lean_ctor_set(v___x_2128_, 1, v_expireTime_2126_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object* v_val_2129_, lean_object* v___f_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___f_2130_);
v_a_2134_ = lean_ctor_get(v_x_2131_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_x_2131_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v_x_2131_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v_x_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 1);
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2165_; 
v_a_2142_ = lean_ctor_get(v_x_2131_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2131_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2144_ = v_x_2131_;
v_isShared_2145_ = v_isSharedCheck_2165_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v_x_2131_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2165_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v_objects_2147_; lean_object* v_expireTime_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2164_; 
v___x_2146_ = lean_st_ref_take(v_val_2129_);
v_objects_2147_ = lean_ctor_get(v___x_2146_, 0);
v_expireTime_2148_ = lean_ctor_get(v___x_2146_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2164_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_expireTime_2148_);
lean_inc(v_objects_2147_);
lean_dec(v___x_2146_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2164_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_2152_, 0, v_expireTime_2148_);
v___x_2153_ = l_Lean_Widget_instToJsonWidgetSource_toJson(v_a_2142_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_objects_2147_);
lean_ctor_set(v___x_2150_, 0, v___x_2153_);
v___x_2155_ = v___x_2150_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_objects_2147_);
v___x_2155_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2156_ = l_Prod_map___redArg(v___f_2130_, v___f_2152_, v___x_2155_);
v_fst_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_fst_2157_);
v_snd_2158_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_snd_2158_);
lean_dec_ref(v___x_2156_);
v___x_2159_ = lean_st_ref_set(v_val_2129_, v_snd_2158_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 0);
lean_ctor_set(v___x_2144_, 0, v_fst_2157_);
v___x_2161_ = v___x_2144_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_fst_2157_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object* v_val_2166_, lean_object* v___f_2167_, lean_object* v_x_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2166_, v___f_2167_, v_x_2168_, v___y_2169_);
lean_dec_ref(v___y_2169_);
lean_dec(v_val_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object* v_method_2179_, lean_object* v_handler_2180_, lean_object* v___f_2181_, uint64_t v_seshId_2182_, lean_object* v_j_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_rpcSessions_2186_; lean_object* v___x_2187_; 
v_rpcSessions_2186_ = lean_ctor_get(v___y_2184_, 0);
v___x_2187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_2186_, v_seshId_2182_);
if (lean_obj_tag(v___x_2187_) == 1)
{
lean_object* v_val_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_val_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_val_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = lean_st_ref_get(v_val_2188_);
lean_dec(v___x_2189_);
lean_inc(v_j_2183_);
v___x_2190_ = l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(v_j_2183_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_val_2188_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___f_2181_);
lean_dec_ref(v_handler_2180_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2211_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2211_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
uint8_t v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2195_ = 3;
v___x_2196_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_2197_ = 1;
v___x_2198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2179_, v___x_2197_);
v___x_2199_ = lean_string_append(v___x_2196_, v___x_2198_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_2201_ = lean_string_append(v___x_2199_, v___x_2200_);
v___x_2202_ = l_Lean_Json_compress(v_j_2183_);
v___x_2203_ = lean_string_append(v___x_2201_, v___x_2202_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_2205_ = lean_string_append(v___x_2203_, v___x_2204_);
v___x_2206_ = lean_string_append(v___x_2205_, v_a_2191_);
lean_dec(v_a_2191_);
v___x_2207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2195_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2207_);
v___x_2209_ = v___x_2193_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2213_; 
lean_dec(v_j_2183_);
lean_dec(v_method_2179_);
v_a_2212_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2190_);
lean_inc_ref(v___y_2184_);
v___x_2213_ = lean_apply_3(v_handler_2180_, v_a_2212_, v___y_2184_, lean_box(0));
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref(v___x_2213_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2215_, 0, v_val_2188_);
lean_closure_set(v___f_2215_, 1, v___f_2181_);
v___x_2216_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_2214_, v___f_2215_, v___y_2184_);
return v___x_2216_;
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_val_2188_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v___f_2181_);
v_a_2217_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2213_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2213_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v___x_2187_);
lean_dec_ref(v___y_2184_);
lean_dec(v_j_2183_);
lean_dec_ref(v___f_2181_);
lean_dec_ref(v_handler_2180_);
lean_dec(v_method_2179_);
v___x_2225_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object* v_method_2227_, lean_object* v_handler_2228_, lean_object* v___f_2229_, lean_object* v_seshId_2230_, lean_object* v_j_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
uint64_t v_seshId_boxed_2234_; lean_object* v_res_2235_; 
v_seshId_boxed_2234_ = lean_unbox_uint64(v_seshId_2230_);
lean_dec_ref(v_seshId_2230_);
v_res_2235_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v_method_2227_, v_handler_2228_, v___f_2229_, v_seshId_boxed_2234_, v_j_2231_, v___y_2232_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_method_2237_, lean_object* v_handler_2238_){
_start:
{
lean_object* v___f_2239_; lean_object* v___f_2240_; 
v___f_2239_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed), 7, 3);
lean_closure_set(v___f_2240_, 0, v_method_2237_);
lean_closure_set(v___f_2240_, 1, v_handler_2238_);
lean_closure_set(v___f_2240_, 2, v___f_2239_);
return v___f_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object* v_method_2245_, lean_object* v_handler_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2282_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2282_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2282_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_errMsg_2258_; uint8_t v___x_2259_; 
v___x_2253_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_2254_ = 1;
lean_inc(v_method_2245_);
v___x_2255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2245_, v___x_2254_);
v___x_2256_ = lean_string_append(v___x_2253_, v___x_2255_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_2258_ = lean_string_append(v___x_2256_, v___x_2257_);
v___x_2259_ = lean_unbox(v_a_2249_);
lean_dec(v_a_2249_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec_ref(v_handler_2246_);
lean_dec(v_method_2245_);
v___x_2260_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_2261_ = lean_string_append(v_errMsg_2258_, v___x_2260_);
v___x_2262_ = lean_mk_io_user_error(v___x_2261_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 1);
lean_ctor_set(v___x_2251_, 0, v___x_2262_);
v___x_2264_ = v___x_2251_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2266_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_2267_ = lean_st_ref_get(v___x_2266_);
v___x_2268_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2267_, v_method_2245_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec_ref(v_errMsg_2258_);
v___x_2269_ = lean_st_ref_take(v___x_2266_);
lean_inc(v_method_2245_);
v___x_2270_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(v_method_2245_, v_handler_2246_);
v___x_2271_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2269_, v_method_2245_, v___x_2270_);
v___x_2272_ = lean_st_ref_set(v___x_2266_, v___x_2271_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2272_);
v___x_2274_ = v___x_2251_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_dec_ref(v_handler_2246_);
lean_dec(v_method_2245_);
v___x_2276_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_2277_ = lean_string_append(v_errMsg_2258_, v___x_2276_);
v___x_2278_ = lean_mk_io_user_error(v___x_2277_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 1);
lean_ctor_set(v___x_2251_, 0, v___x_2278_);
v___x_2280_ = v___x_2251_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_handler_2246_);
lean_dec(v_method_2245_);
v_a_2283_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2248_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2248_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2291_, lean_object* v_handler_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2291_, v_handler_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2303_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2304_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v___x_2302_, v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
return v_res_2306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
uint8_t v___x_2310_; 
v___x_2310_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2308_, v_x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2311_, v_x_2312_, v_x_2313_);
lean_dec(v_x_2313_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_2316_){
_start:
{
lean_inc_ref(v_x_2316_);
return v_x_2316_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2317_);
lean_dec_ref(v_x_2317_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2319_, lean_object* v_x_2320_, lean_object* v___y_2321_){
_start:
{
lean_inc_ref(v_x_2320_);
return v_x_2320_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_x_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b1_2322_, v_x_2323_, v___y_2324_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_x_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2327_, v_x_2328_, v_x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2331_, lean_object* v_x_2332_, size_t v_x_2333_, lean_object* v_x_2334_){
_start:
{
uint8_t v___x_2335_; 
v___x_2335_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2332_, v_x_2333_, v_x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
size_t v_x_1765__boxed_2340_; uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_x_1765__boxed_2340_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2341_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2336_, v_x_2337_, v_x_1765__boxed_2340_, v_x_2339_);
lean_dec(v_x_2339_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, size_t v_x_2345_, size_t v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
size_t v_x_1776__boxed_2356_; size_t v_x_1777__boxed_2357_; lean_object* v_res_2358_; 
v_x_1776__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_x_1777__boxed_2357_ = lean_unbox_usize(v_x_2353_);
lean_dec(v_x_2353_);
v_res_2358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_2350_, v_x_2351_, v_x_1776__boxed_2356_, v_x_1777__boxed_2357_, v_x_2354_, v_x_2355_);
return v_res_2358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2359_, lean_object* v_keys_2360_, lean_object* v_vals_2361_, lean_object* v_heq_2362_, lean_object* v_i_2363_, lean_object* v_k_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2360_, v_i_2363_, v_k_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2366_, lean_object* v_keys_2367_, lean_object* v_vals_2368_, lean_object* v_heq_2369_, lean_object* v_i_2370_, lean_object* v_k_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2366_, v_keys_2367_, v_vals_2368_, v_heq_2369_, v_i_2370_, v_k_2371_);
lean_dec(v_k_2371_);
lean_dec_ref(v_vals_2368_);
lean_dec_ref(v_keys_2367_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_2374_, lean_object* v_n_2375_, lean_object* v_k_2376_, lean_object* v_v_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v_n_2375_, v_k_2376_, v_v_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2379_, size_t v_depth_2380_, lean_object* v_keys_2381_, lean_object* v_vals_2382_, lean_object* v_heq_2383_, lean_object* v_i_2384_, lean_object* v_entries_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2380_, v_keys_2381_, v_vals_2382_, v_i_2384_, v_entries_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2387_, lean_object* v_depth_2388_, lean_object* v_keys_2389_, lean_object* v_vals_2390_, lean_object* v_heq_2391_, lean_object* v_i_2392_, lean_object* v_entries_2393_){
_start:
{
size_t v_depth_boxed_2394_; lean_object* v_res_2395_; 
v_depth_boxed_2394_ = lean_unbox_usize(v_depth_2388_);
lean_dec(v_depth_2388_);
v_res_2395_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(v_00_u03b2_2387_, v_depth_boxed_2394_, v_keys_2389_, v_vals_2390_, v_heq_2391_, v_i_2392_, v_entries_2393_);
lean_dec_ref(v_vals_2390_);
lean_dec_ref(v_keys_2389_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_, lean_object* v_x_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_x_2397_, v_x_2398_, v_x_2399_, v_x_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(lean_object* v_x_2402_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_unsigned_to_nat(0u);
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_unsigned_to_nat(1u);
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___boxed(lean_object* v_x_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(v_x_2405_);
lean_dec_ref(v_x_2405_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object* v_t_2407_, lean_object* v_k_2408_){
_start:
{
if (lean_obj_tag(v_t_2407_) == 0)
{
lean_object* v_n_2409_; lean_object* v___x_2410_; 
v_n_2409_ = lean_ctor_get(v_t_2407_, 0);
lean_inc(v_n_2409_);
lean_dec_ref(v_t_2407_);
v___x_2410_ = lean_apply_1(v_k_2408_, v_n_2409_);
return v___x_2410_;
}
else
{
lean_object* v_wi_2411_; lean_object* v___x_2412_; 
v_wi_2411_ = lean_ctor_get(v_t_2407_, 0);
lean_inc_ref(v_wi_2411_);
lean_dec_ref(v_t_2407_);
v___x_2412_ = lean_apply_1(v_k_2408_, v_wi_2411_);
return v___x_2412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object* v_motive_2413_, lean_object* v_ctorIdx_2414_, lean_object* v_t_2415_, lean_object* v_h_2416_, lean_object* v_k_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2415_, v_k_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object* v_motive_2419_, lean_object* v_ctorIdx_2420_, lean_object* v_t_2421_, lean_object* v_h_2422_, lean_object* v_k_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(v_motive_2419_, v_ctorIdx_2420_, v_t_2421_, v_h_2422_, v_k_2423_);
lean_dec(v_ctorIdx_2420_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object* v_t_2425_, lean_object* v_global_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2425_, v_global_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object* v_motive_2428_, lean_object* v_t_2429_, lean_object* v_h_2430_, lean_object* v_global_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2429_, v_global_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object* v_t_2433_, lean_object* v_local_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2433_, v_local_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object* v_motive_2436_, lean_object* v_t_2437_, lean_object* v_h_2438_, lean_object* v_local_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2437_, v_local_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2441_, uint64_t v_k_2442_, lean_object* v_fallback_2443_){
_start:
{
if (lean_obj_tag(v_t_2441_) == 0)
{
lean_object* v_k_2444_; lean_object* v_v_2445_; lean_object* v_l_2446_; lean_object* v_r_2447_; uint64_t v___x_2448_; uint8_t v___x_2449_; 
v_k_2444_ = lean_ctor_get(v_t_2441_, 1);
v_v_2445_ = lean_ctor_get(v_t_2441_, 2);
v_l_2446_ = lean_ctor_get(v_t_2441_, 3);
v_r_2447_ = lean_ctor_get(v_t_2441_, 4);
v___x_2448_ = lean_unbox_uint64(v_k_2444_);
v___x_2449_ = lean_uint64_dec_lt(v_k_2442_, v___x_2448_);
if (v___x_2449_ == 0)
{
uint64_t v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = lean_unbox_uint64(v_k_2444_);
v___x_2451_ = lean_uint64_dec_eq(v_k_2442_, v___x_2450_);
if (v___x_2451_ == 0)
{
v_t_2441_ = v_r_2447_;
goto _start;
}
else
{
lean_inc(v_v_2445_);
return v_v_2445_;
}
}
else
{
v_t_2441_ = v_l_2446_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2443_);
return v_fallback_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2454_, lean_object* v_k_2455_, lean_object* v_fallback_2456_){
_start:
{
uint64_t v_k_boxed_2457_; lean_object* v_res_2458_; 
v_k_boxed_2457_ = lean_unbox_uint64(v_k_2455_);
lean_dec_ref(v_k_2455_);
v_res_2458_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2454_, v_k_boxed_2457_, v_fallback_2456_);
lean_dec(v_fallback_2456_);
lean_dec(v_t_2454_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_s_2459_, lean_object* v_x_2460_){
_start:
{
lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2475_; 
v_fst_2461_ = lean_ctor_get(v_x_2460_, 0);
v_snd_2462_ = lean_ctor_get(v_x_2460_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2464_ = v_x_2460_;
v_isShared_2465_ = v_isSharedCheck_2475_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_snd_2462_);
lean_inc(v_fst_2461_);
lean_dec(v_x_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2475_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; uint64_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_snd_2462_);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_unbox_uint64(v_fst_2461_);
v___x_2469_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_s_2459_, v___x_2468_, v___x_2467_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 1);
lean_ctor_set(v___x_2464_, 1, v___x_2469_);
lean_ctor_set(v___x_2464_, 0, v___x_2466_);
v___x_2471_ = v___x_2464_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
uint64_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_unbox_uint64(v_fst_2461_);
lean_dec(v_fst_2461_);
v___x_2473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_2472_, v___x_2471_, v_s_2459_);
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(uint8_t v_x_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2478_, 0, v___y_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_x_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_x_240__boxed_2481_; lean_object* v_res_2482_; 
v_x_240__boxed_2481_ = lean_unbox(v_x_2479_);
v_res_2482_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v_x_240__boxed_2481_, v___y_2480_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v___y_2483_){
_start:
{
lean_inc(v___y_2483_);
return v___y_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v___y_2484_);
lean_dec(v___y_2484_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_));
v___x_2501_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2504_, lean_object* v_t_2505_, uint64_t v_k_2506_, lean_object* v_fallback_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2505_, v_k_2506_, v_fallback_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2509_, lean_object* v_t_2510_, lean_object* v_k_2511_, lean_object* v_fallback_2512_){
_start:
{
uint64_t v_k_boxed_2513_; lean_object* v_res_2514_; 
v_k_boxed_2513_ = lean_unbox_uint64(v_k_2511_);
lean_dec_ref(v_k_2511_);
v_res_2514_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(v_00_u03b4_2509_, v_t_2510_, v_k_boxed_2513_, v_fallback_2512_);
lean_dec(v_fallback_2512_);
lean_dec(v_t_2510_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(lean_object* v_as_x27_2515_, lean_object* v_b_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
if (lean_obj_tag(v_as_x27_2515_) == 0)
{
lean_object* v___x_2522_; 
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2516_);
return v___x_2522_;
}
else
{
lean_object* v_head_2523_; 
v_head_2523_ = lean_ctor_get(v_as_x27_2515_, 0);
lean_inc(v_head_2523_);
if (lean_obj_tag(v_head_2523_) == 0)
{
lean_object* v_tail_2524_; lean_object* v_n_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_tail_2524_ = lean_ctor_get(v_as_x27_2515_, 1);
lean_inc(v_tail_2524_);
lean_dec_ref(v_as_x27_2515_);
v_n_2525_ = lean_ctor_get(v_head_2523_, 0);
lean_inc(v_n_2525_);
lean_dec_ref(v_head_2523_);
v___x_2526_ = lean_box(0);
v___x_2527_ = l_Lean_mkConst(v_n_2525_, v___x_2526_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
v___x_2528_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v___x_2527_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = lean_array_push(v_b_2516_, v_a_2529_);
v_as_x27_2515_ = v_tail_2524_;
v_b_2516_ = v___x_2530_;
goto _start;
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_tail_2524_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v_b_2516_);
v_a_2532_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2528_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2528_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_tail_2540_; lean_object* v_wi_2541_; lean_object* v___x_2542_; 
v_tail_2540_ = lean_ctor_get(v_as_x27_2515_, 1);
lean_inc(v_tail_2540_);
lean_dec_ref(v_as_x27_2515_);
v_wi_2541_ = lean_ctor_get(v_head_2523_, 0);
lean_inc_ref(v_wi_2541_);
lean_dec_ref(v_head_2523_);
v___x_2542_ = lean_array_push(v_b_2516_, v_wi_2541_);
v_as_x27_2515_ = v_tail_2540_;
v_b_2516_ = v___x_2542_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg___boxed(lean_object* v_as_x27_2544_, lean_object* v_b_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2544_, v_b_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(lean_object* v_init_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v_v_2559_; lean_object* v_l_2560_; lean_object* v_r_2561_; lean_object* v___x_2562_; 
v_v_2559_ = lean_ctor_get(v_x_2553_, 2);
lean_inc(v_v_2559_);
v_l_2560_ = lean_ctor_get(v_x_2553_, 3);
lean_inc(v_l_2560_);
v_r_2561_ = lean_ctor_get(v_x_2553_, 4);
lean_inc(v_r_2561_);
lean_dec_ref(v_x_2553_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
v___x_2562_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2552_, v_l_2560_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
v_a_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_a_2564_);
lean_dec(v_a_2563_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
v___x_2565_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_v_2559_, v_a_2564_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref(v___x_2565_);
v_init_2552_ = v_a_2566_;
v_x_2553_ = v_r_2561_;
goto _start;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_r_2561_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
v_a_2568_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2565_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2565_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_dec(v_r_2561_);
lean_dec(v_v_2559_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v___x_2562_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v_init_2552_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1___boxed(lean_object* v_init_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2578_, v_x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets(lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v_env_2594_; lean_object* v___x_2595_; lean_object* v_ext_2596_; lean_object* v_toEnvExtension_2597_; lean_object* v_asyncMode_2598_; lean_object* v_ret_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2593_ = lean_st_ref_get(v_a_2591_);
v_env_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_ref(v_env_2594_);
lean_dec(v___x_2593_);
v___x_2595_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v_ext_2596_ = lean_ctor_get(v___x_2595_, 1);
lean_inc_ref(v_ext_2596_);
v_toEnvExtension_2597_ = lean_ctor_get(v_ext_2596_, 0);
lean_inc_ref(v_toEnvExtension_2597_);
lean_dec_ref(v_ext_2596_);
v_asyncMode_2598_ = lean_ctor_get(v_toEnvExtension_2597_, 2);
lean_inc(v_asyncMode_2598_);
lean_dec_ref(v_toEnvExtension_2597_);
v_ret_2599_ = ((lean_object*)(l_Lean_Widget_evalPanelWidgets___closed__0));
v___x_2600_ = lean_box(1);
v___x_2601_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2600_, v___x_2595_, v_env_2594_, v_asyncMode_2598_);
lean_dec(v_asyncMode_2598_);
v___x_2602_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_ret_2599_, v___x_2601_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2611_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_a_2607_; lean_object* v___x_2609_; 
v_a_2607_ = lean_ctor_get(v_a_2603_, 0);
lean_inc(v_a_2607_);
lean_dec(v_a_2603_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v_a_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
v_a_2612_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2602_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2602_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Widget_evalPanelWidgets(v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object* v_as_2626_, lean_object* v_as_x27_2627_, lean_object* v_b_2628_, lean_object* v_a_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2627_, v_b_2628_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object* v_as_2636_, lean_object* v_as_x27_2637_, lean_object* v_b_2638_, lean_object* v_a_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2636_, v_as_x27_2637_, v_b_2638_, v_a_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v_as_2636_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, uint64_t v_h_2649_, lean_object* v_n_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2651_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2652_ = lean_box_uint64(v_h_2649_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v_n_2650_);
v___x_2654_ = 0;
v___x_2655_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2646_, v_inst_2648_, v_inst_2647_, v___x_2651_, v___x_2653_, v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_h_2659_, lean_object* v_n_2660_){
_start:
{
uint64_t v_h_boxed_2661_; lean_object* v_res_2662_; 
v_h_boxed_2661_ = lean_unbox_uint64(v_h_2659_);
lean_dec_ref(v_h_2659_);
v_res_2662_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2656_, v_inst_2657_, v_inst_2658_, v_h_boxed_2661_, v_n_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object* v_m_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, uint64_t v_h_2667_, lean_object* v_n_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_h_2667_, v_n_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object* v_m_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_h_2674_, lean_object* v_n_2675_){
_start:
{
uint64_t v_h_boxed_2676_; lean_object* v_res_2677_; 
v_h_boxed_2676_ = lean_unbox_uint64(v_h_2674_);
lean_dec_ref(v_h_2674_);
v_res_2677_ = l_Lean_Widget_addPanelWidgetGlobal(v_m_2670_, v_inst_2671_, v_inst_2672_, v_inst_2673_, v_h_boxed_2676_, v_n_2675_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, uint64_t v_h_2681_, lean_object* v_n_2682_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___x_2687_; 
v___x_2683_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2684_ = lean_box_uint64(v_h_2681_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v_n_2682_);
v___x_2686_ = 2;
v___x_2687_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2678_, v_inst_2680_, v_inst_2679_, v___x_2683_, v___x_2685_, v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_h_2691_, lean_object* v_n_2692_){
_start:
{
uint64_t v_h_boxed_2693_; lean_object* v_res_2694_; 
v_h_boxed_2693_ = lean_unbox_uint64(v_h_2691_);
lean_dec_ref(v_h_2691_);
v_res_2694_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2688_, v_inst_2689_, v_inst_2690_, v_h_boxed_2693_, v_n_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object* v_m_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, uint64_t v_h_2699_, lean_object* v_n_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2696_, v_inst_2697_, v_inst_2698_, v_h_2699_, v_n_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_h_2706_, lean_object* v_n_2707_){
_start:
{
uint64_t v_h_boxed_2708_; lean_object* v_res_2709_; 
v_h_boxed_2708_ = lean_unbox_uint64(v_h_2706_);
lean_dec_ref(v_h_2706_);
v_res_2709_ = l_Lean_Widget_addPanelWidgetScoped(v_m_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_h_boxed_2708_, v_n_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t v_x_2710_, uint64_t v_y_2711_){
_start:
{
uint8_t v___x_2712_; 
v___x_2712_ = lean_uint64_dec_lt(v_x_2710_, v_y_2711_);
if (v___x_2712_ == 0)
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_uint64_dec_eq(v_x_2710_, v_y_2711_);
if (v___x_2713_ == 0)
{
uint8_t v___x_2714_; 
v___x_2714_ = 2;
return v___x_2714_;
}
else
{
uint8_t v___x_2715_; 
v___x_2715_ = 1;
return v___x_2715_;
}
}
else
{
uint8_t v___x_2716_; 
v___x_2716_ = 0;
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object* v_x_2717_, lean_object* v_y_2718_){
_start:
{
uint64_t v_x_boxed_2719_; uint64_t v_y_boxed_2720_; uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_x_boxed_2719_ = lean_unbox_uint64(v_x_2717_);
lean_dec_ref(v_x_2717_);
v_y_boxed_2720_ = lean_unbox_uint64(v_y_2718_);
lean_dec_ref(v_y_2718_);
v_res_2721_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_boxed_2719_, v_y_boxed_2720_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object* v_wi_2723_, lean_object* v___f_2724_, lean_object* v_s_2725_){
_start:
{
uint64_t v_javascriptHash_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_javascriptHash_2726_ = lean_ctor_get_uint64(v_wi_2723_, sizeof(void*)*2);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_wi_2723_);
v___x_2728_ = lean_box(0);
v___x_2729_ = lean_box_uint64(v_javascriptHash_2726_);
lean_inc(v_s_2725_);
lean_inc_ref(v___f_2724_);
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___f_2724_, v_s_2725_, v___x_2729_, v___x_2728_);
v___x_2731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2727_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_box_uint64(v_javascriptHash_2726_);
v___x_2733_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2724_, v___x_2732_, v___x_2731_, v_s_2725_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object* v___f_2734_, lean_object* v_env_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2737_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2736_, v_env_2735_, v___f_2734_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object* v_inst_2739_, lean_object* v_wi_2740_){
_start:
{
lean_object* v_modifyEnv_2741_; lean_object* v___f_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___x_2745_; 
v_modifyEnv_2741_ = lean_ctor_get(v_inst_2739_, 1);
lean_inc(v_modifyEnv_2741_);
lean_dec_ref(v_inst_2739_);
v___f_2742_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___f_2743_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2743_, 0, v_wi_2740_);
lean_closure_set(v___f_2743_, 1, v___f_2742_);
v___f_2744_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2744_, 0, v___f_2743_);
v___x_2745_ = lean_apply_1(v_modifyEnv_2741_, v___f_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object* v_m_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_wi_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Widget_addPanelWidgetLocal___redArg(v_inst_2748_, v_wi_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object* v_m_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_wi_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Widget_addPanelWidgetLocal(v_m_2751_, v_inst_2752_, v_inst_2753_, v_wi_2754_);
lean_dec_ref(v_inst_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object* v___f_2756_, uint64_t v_h_2757_, lean_object* v_st_2758_){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_box_uint64(v_h_2757_);
v___x_2760_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___f_2756_, v___x_2759_, v_st_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object* v___f_2761_, lean_object* v_h_2762_, lean_object* v_st_2763_){
_start:
{
uint64_t v_h_boxed_2764_; lean_object* v_res_2765_; 
v_h_boxed_2764_ = lean_unbox_uint64(v_h_2762_);
lean_dec_ref(v_h_2762_);
v_res_2765_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2761_, v_h_boxed_2764_, v_st_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object* v_inst_2766_, uint64_t v_h_2767_){
_start:
{
lean_object* v_modifyEnv_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___x_2773_; 
v_modifyEnv_2768_ = lean_ctor_get(v_inst_2766_, 1);
lean_inc(v_modifyEnv_2768_);
lean_dec_ref(v_inst_2766_);
v___f_2769_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___x_2770_ = lean_box_uint64(v_h_2767_);
v___f_2771_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2771_, 0, v___f_2769_);
lean_closure_set(v___f_2771_, 1, v___x_2770_);
v___f_2772_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2772_, 0, v___f_2771_);
v___x_2773_ = lean_apply_1(v_modifyEnv_2768_, v___f_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object* v_inst_2774_, lean_object* v_h_2775_){
_start:
{
uint64_t v_h_boxed_2776_; lean_object* v_res_2777_; 
v_h_boxed_2776_ = lean_unbox_uint64(v_h_2775_);
lean_dec_ref(v_h_2775_);
v_res_2777_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2774_, v_h_boxed_2776_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget(lean_object* v_m_2778_, lean_object* v_inst_2779_, lean_object* v_inst_2780_, uint64_t v_h_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2780_, v_h_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object* v_m_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_h_2786_){
_start:
{
uint64_t v_h_boxed_2787_; lean_object* v_res_2788_; 
v_h_boxed_2787_ = lean_unbox_uint64(v_h_2786_);
lean_dec_ref(v_h_2786_);
v_res_2788_ = l_Lean_Widget_erasePanelWidget(v_m_2783_, v_inst_2784_, v_inst_2785_, v_h_boxed_2787_);
lean_dec_ref(v_inst_2784_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t v_hash_2789_, lean_object* v_props_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_val_2798_; lean_object* v_env_2801_; lean_object* v___x_2802_; 
v___x_2794_ = lean_st_ref_get(v_a_2792_);
v___x_2795_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_2796_ = lean_st_ref_get(v___x_2795_);
v_env_2801_ = lean_ctor_get(v___x_2794_, 0);
lean_inc_ref(v_env_2801_);
lean_dec(v___x_2794_);
v___x_2802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_2796_, v_hash_2789_);
lean_dec(v___x_2796_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v___x_2803_; lean_object* v_toEnvExtension_2804_; lean_object* v_asyncMode_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2803_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc_ref(v_toEnvExtension_2804_);
v_asyncMode_2805_ = lean_ctor_get(v_toEnvExtension_2804_, 2);
lean_inc(v_asyncMode_2805_);
lean_dec_ref(v_toEnvExtension_2804_);
v___x_2806_ = lean_box(1);
v___x_2807_ = lean_box(0);
v___x_2808_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2806_, v___x_2803_, v_env_2801_, v_asyncMode_2805_, v___x_2807_);
lean_dec(v_asyncMode_2805_);
v___x_2809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_2808_, v_hash_2789_);
lean_dec(v___x_2808_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_props_2790_);
v___x_2810_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_2811_ = lean_uint64_to_nat(v_hash_2789_);
v___x_2812_ = l_Nat_reprFast(v___x_2811_);
v___x_2813_ = lean_string_append(v___x_2810_, v___x_2812_);
lean_dec_ref(v___x_2812_);
v___x_2814_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_2815_ = lean_string_append(v___x_2813_, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
v___x_2817_ = l_Lean_MessageData_ofFormat(v___x_2816_);
v___x_2818_ = l_Lean_throwError___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v___x_2817_, v_a_2791_, v_a_2792_);
return v___x_2818_;
}
else
{
lean_object* v_val_2819_; lean_object* v_fst_2820_; 
v_val_2819_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2819_);
lean_dec_ref(v___x_2809_);
v_fst_2820_ = lean_ctor_get(v_val_2819_, 0);
lean_inc(v_fst_2820_);
lean_dec(v_val_2819_);
v_val_2798_ = v_fst_2820_;
goto v___jp_2797_;
}
}
else
{
lean_object* v_val_2821_; lean_object* v_fst_2822_; 
lean_dec_ref(v_env_2801_);
v_val_2821_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v___x_2802_);
v_fst_2822_ = lean_ctor_get(v_val_2821_, 0);
lean_inc(v_fst_2822_);
lean_dec(v_val_2821_);
v_val_2798_ = v_fst_2822_;
goto v___jp_2797_;
}
v___jp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2799_, 0, v_val_2798_);
lean_ctor_set(v___x_2799_, 1, v_props_2790_);
lean_ctor_set_uint64(v___x_2799_, sizeof(void*)*2, v_hash_2789_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object* v_hash_2823_, lean_object* v_props_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
uint64_t v_hash_boxed_2828_; lean_object* v_res_2829_; 
v_hash_boxed_2828_ = lean_unbox_uint64(v_hash_2823_);
lean_dec_ref(v_hash_2823_);
v_res_2829_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_boxed_2828_, v_props_2824_, v_a_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object* v_t_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; lean_object* v_infoState_2834_; uint8_t v_enabled_2835_; 
v___x_2833_ = lean_st_ref_get(v___y_2831_);
v_infoState_2834_ = lean_ctor_get(v___x_2833_, 7);
lean_inc_ref(v_infoState_2834_);
lean_dec(v___x_2833_);
v_enabled_2835_ = lean_ctor_get_uint8(v_infoState_2834_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2834_);
if (v_enabled_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec_ref(v_t_2830_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
else
{
lean_object* v___x_2838_; lean_object* v_infoState_2839_; lean_object* v_env_2840_; lean_object* v_nextMacroScope_2841_; lean_object* v_ngen_2842_; lean_object* v_auxDeclNGen_2843_; lean_object* v_traceState_2844_; lean_object* v_cache_2845_; lean_object* v_messages_2846_; lean_object* v_snapshotTasks_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2869_; 
v___x_2838_ = lean_st_ref_take(v___y_2831_);
v_infoState_2839_ = lean_ctor_get(v___x_2838_, 7);
v_env_2840_ = lean_ctor_get(v___x_2838_, 0);
v_nextMacroScope_2841_ = lean_ctor_get(v___x_2838_, 1);
v_ngen_2842_ = lean_ctor_get(v___x_2838_, 2);
v_auxDeclNGen_2843_ = lean_ctor_get(v___x_2838_, 3);
v_traceState_2844_ = lean_ctor_get(v___x_2838_, 4);
v_cache_2845_ = lean_ctor_get(v___x_2838_, 5);
v_messages_2846_ = lean_ctor_get(v___x_2838_, 6);
v_snapshotTasks_2847_ = lean_ctor_get(v___x_2838_, 8);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2849_ = v___x_2838_;
v_isShared_2850_ = v_isSharedCheck_2869_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snapshotTasks_2847_);
lean_inc(v_infoState_2839_);
lean_inc(v_messages_2846_);
lean_inc(v_cache_2845_);
lean_inc(v_traceState_2844_);
lean_inc(v_auxDeclNGen_2843_);
lean_inc(v_ngen_2842_);
lean_inc(v_nextMacroScope_2841_);
lean_inc(v_env_2840_);
lean_dec(v___x_2838_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2869_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint8_t v_enabled_2851_; lean_object* v_assignment_2852_; lean_object* v_lazyAssignment_2853_; lean_object* v_trees_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2868_; 
v_enabled_2851_ = lean_ctor_get_uint8(v_infoState_2839_, sizeof(void*)*3);
v_assignment_2852_ = lean_ctor_get(v_infoState_2839_, 0);
v_lazyAssignment_2853_ = lean_ctor_get(v_infoState_2839_, 1);
v_trees_2854_ = lean_ctor_get(v_infoState_2839_, 2);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_infoState_2839_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2856_ = v_infoState_2839_;
v_isShared_2857_ = v_isSharedCheck_2868_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_trees_2854_);
lean_inc(v_lazyAssignment_2853_);
lean_inc(v_assignment_2852_);
lean_dec(v_infoState_2839_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2868_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = l_Lean_PersistentArray_push___redArg(v_trees_2854_, v_t_2830_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 2, v___x_2858_);
v___x_2860_ = v___x_2856_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_assignment_2852_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_lazyAssignment_2853_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v___x_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2867_, sizeof(void*)*3, v_enabled_2851_);
v___x_2860_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 7, v___x_2860_);
v___x_2862_ = v___x_2849_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_env_2840_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_nextMacroScope_2841_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_ngen_2842_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_auxDeclNGen_2843_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v_traceState_2844_);
lean_ctor_set(v_reuseFailAlloc_2866_, 5, v_cache_2845_);
lean_ctor_set(v_reuseFailAlloc_2866_, 6, v_messages_2846_);
lean_ctor_set(v_reuseFailAlloc_2866_, 7, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2866_, 8, v_snapshotTasks_2847_);
v___x_2862_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_st_ref_set(v___y_2831_, v___x_2862_);
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2870_, v___y_2871_);
lean_dec(v___y_2871_);
return v_res_2873_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_unsigned_to_nat(32u);
v___x_2875_ = lean_mk_empty_array_with_capacity(v___x_2874_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2877_ = ((size_t)5ULL);
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = lean_unsigned_to_nat(32u);
v___x_2880_ = lean_mk_empty_array_with_capacity(v___x_2879_);
v___x_2881_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0);
v___x_2882_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2880_);
lean_ctor_set(v___x_2882_, 2, v___x_2878_);
lean_ctor_set(v___x_2882_, 3, v___x_2878_);
lean_ctor_set_usize(v___x_2882_, 4, v___x_2877_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object* v_t_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; lean_object* v_infoState_2888_; uint8_t v_enabled_2889_; 
v___x_2887_ = lean_st_ref_get(v___y_2885_);
v_infoState_2888_ = lean_ctor_get(v___x_2887_, 7);
lean_inc_ref(v_infoState_2888_);
lean_dec(v___x_2887_);
v_enabled_2889_ = lean_ctor_get_uint8(v_infoState_2888_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2888_);
if (v_enabled_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec_ref(v_t_2883_);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1);
v___x_2893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_t_2883_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v___x_2893_, v___y_2885_);
return v___x_2894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object* v_t_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t v_hash_2900_, lean_object* v_props_2901_, lean_object* v_stx_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2900_, v_props_2901_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2907_);
lean_ctor_set(v___x_2908_, 1, v_stx_2902_);
v___x_2909_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
v___x_2910_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v___x_2909_, v_a_2903_, v_a_2904_);
return v___x_2910_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_stx_2902_);
v_a_2911_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2906_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2906_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object* v_hash_2919_, lean_object* v_props_2920_, lean_object* v_stx_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
uint64_t v_hash_boxed_2925_; lean_object* v_res_2926_; 
v_hash_boxed_2925_ = lean_unbox_uint64(v_hash_2919_);
lean_dec_ref(v_hash_2919_);
v_res_2926_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_boxed_2925_, v_props_2920_, v_stx_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object* v_t_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2927_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object* v_t_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2936_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedUserWidgetDefinition_default(void){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_obj_once(&l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0, &l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_once, _init_l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedUserWidgetDefinition(void){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Widget_instInhabitedUserWidgetDefinition_default;
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object* v_x_2943_){
_start:
{
lean_object* v_name_2944_; lean_object* v_javascript_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2965_; 
v_name_2944_ = lean_ctor_get(v_x_2943_, 0);
v_javascript_2945_ = lean_ctor_get(v_x_2943_, 1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2947_ = v_x_2943_;
v_isShared_2948_ = v_isSharedCheck_2965_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_javascript_2945_);
lean_inc(v_name_2944_);
lean_dec(v_x_2943_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2965_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2949_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_2950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_name_2944_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2950_);
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_2956_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_javascript_2945_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v___x_2953_);
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2953_);
v___x_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2954_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_2962_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_2960_, v___x_2961_);
v___x_2963_ = l_Lean_Json_mkObj(v___x_2962_);
return v___x_2963_;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = 1;
v___x_2974_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_2975_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2974_, v___x_2973_);
return v___x_2975_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = ((lean_object*)(l_Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_2977_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2);
v___x_2978_ = lean_string_append(v___x_2977_, v___x_2976_);
return v___x_2978_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = 1;
v___x_2982_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4));
v___x_2983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2982_, v___x_2981_);
return v___x_2983_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5);
v___x_2985_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2986_ = lean_string_append(v___x_2985_, v___x_2984_);
return v___x_2986_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2988_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6);
v___x_2989_ = lean_string_append(v___x_2988_, v___x_2987_);
return v___x_2989_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = 1;
v___x_2993_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8));
v___x_2994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2993_, v___x_2992_);
return v___x_2994_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9);
v___x_2996_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2997_ = lean_string_append(v___x_2996_, v___x_2995_);
return v___x_2997_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2998_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2999_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10);
v___x_3000_ = lean_string_append(v___x_2999_, v___x_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object* v_json_3001_){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
lean_inc(v_json_3001_);
v___x_3003_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3001_, v___x_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v_json_3001_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3006_ = v___x_3003_;
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7);
v___x_3009_ = lean_string_append(v___x_3008_, v_a_3004_);
lean_dec(v_a_3004_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3009_);
v___x_3011_ = v___x_3006_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
else
{
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_json_3001_);
v_a_3014_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3003_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3003_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 0);
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3003_);
v___x_3023_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_3024_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3001_, v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_a_3022_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3034_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3034_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3029_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11);
v___x_3030_ = lean_string_append(v___x_3029_, v_a_3025_);
lean_dec(v_a_3025_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3030_);
v___x_3032_ = v___x_3027_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
else
{
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_3022_);
v_a_3035_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3024_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3024_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 0);
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_a_3043_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v___x_3024_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3024_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v_a_3022_);
lean_ctor_set(v___x_3047_, 1, v_a_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object* v_uwd_3054_){
_start:
{
lean_object* v_javascript_3055_; uint64_t v___x_3056_; lean_object* v___x_3057_; 
v_javascript_3055_ = lean_ctor_get(v_uwd_3054_, 1);
v___x_3056_ = lean_string_hash(v_javascript_3055_);
lean_inc_ref(v_javascript_3055_);
v___x_3057_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3057_, 0, v_javascript_3055_);
lean_ctor_set_uint64(v___x_3057_, sizeof(void*)*1, v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object* v_uwd_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(v_uwd_3058_);
lean_dec_ref(v_uwd_3058_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object* v_____do__lift_3062_, lean_object* v_id_3063_, lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v___x_3066_, lean_object* v_____do__lift_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3069_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_3062_, v_____do__lift_3067_, v___x_3068_, v_id_3063_);
v___x_3070_ = l_Lean_ofExcept___redArg(v_inst_3064_, v_inst_3065_, v___x_3066_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object* v_____do__lift_3071_, lean_object* v_id_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v___x_3075_, lean_object* v_____do__lift_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(v_____do__lift_3071_, v_id_3072_, v_inst_3073_, v_inst_3074_, v___x_3075_, v_____do__lift_3076_);
lean_dec_ref(v_____do__lift_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object* v_id_3078_, lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v___x_3081_, lean_object* v_toBind_3082_, lean_object* v_inst_3083_, lean_object* v_____do__lift_3084_){
_start:
{
lean_object* v___f_3085_; lean_object* v___x_3086_; 
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_3085_, 0, v_____do__lift_3084_);
lean_closure_set(v___f_3085_, 1, v_id_3078_);
lean_closure_set(v___f_3085_, 2, v_inst_3079_);
lean_closure_set(v___f_3085_, 3, v_inst_3080_);
lean_closure_set(v___f_3085_, 4, v___x_3081_);
v___x_3086_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v_inst_3083_, v___f_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_id_3092_){
_start:
{
lean_object* v_toBind_3093_; lean_object* v_getEnv_3094_; lean_object* v___x_3095_; lean_object* v___f_3096_; lean_object* v___x_3097_; 
v_toBind_3093_ = lean_ctor_get(v_inst_3088_, 1);
lean_inc(v_toBind_3093_);
v_getEnv_3094_ = lean_ctor_get(v_inst_3089_, 0);
lean_inc(v_getEnv_3094_);
lean_dec_ref(v_inst_3089_);
v___x_3095_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0));
lean_inc(v_toBind_3093_);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3096_, 0, v_id_3092_);
lean_closure_set(v___f_3096_, 1, v_inst_3088_);
lean_closure_set(v___f_3096_, 2, v_inst_3091_);
lean_closure_set(v___f_3096_, 3, v___x_3095_);
lean_closure_set(v___f_3096_, 4, v_toBind_3093_);
lean_closure_set(v___f_3096_, 5, v_inst_3090_);
v___x_3097_ = lean_apply_4(v_toBind_3093_, lean_box(0), lean_box(0), v_getEnv_3094_, v___f_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object* v_m_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_id_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(v_inst_3099_, v_inst_3100_, v_inst_3101_, v_inst_3102_, v_id_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object* v_text_3105_, lean_object* v_hoverLine_3106_, lean_object* v_x_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 9)
{
lean_object* v_i_3110_; lean_object* v___x_3111_; 
v_i_3110_ = lean_ctor_get(v_x_3108_, 0);
v___x_3111_ = l_Lean_Elab_Info_pos_x3f(v_x_3108_);
if (lean_obj_tag(v___x_3111_) == 1)
{
lean_object* v_val_3112_; lean_object* v___x_3113_; 
v_val_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_val_3112_);
lean_dec_ref(v___x_3111_);
v___x_3113_ = l_Lean_Elab_Info_tailPos_x3f(v_x_3108_);
if (lean_obj_tag(v___x_3113_) == 1)
{
lean_object* v_val_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3129_; 
v_val_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3129_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_val_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3129_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v_line_3119_; uint8_t v___x_3120_; 
lean_inc_ref(v_text_3105_);
v___x_3118_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3105_, v_val_3112_);
lean_dec(v_val_3112_);
v_line_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_line_3119_);
lean_dec_ref(v___x_3118_);
v___x_3120_ = lean_nat_dec_le(v_line_3119_, v_hoverLine_3106_);
lean_dec(v_line_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_del_object(v___x_3116_);
lean_dec(v_val_3114_);
lean_dec_ref(v_text_3105_);
v___x_3121_ = lean_box(0);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v_line_3123_; uint8_t v___x_3124_; 
v___x_3122_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3105_, v_val_3114_);
lean_dec(v_val_3114_);
v_line_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_line_3123_);
lean_dec_ref(v___x_3122_);
v___x_3124_ = lean_nat_dec_le(v_hoverLine_3106_, v_line_3123_);
lean_dec(v_line_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_del_object(v___x_3116_);
v___x_3125_ = lean_box(0);
return v___x_3125_;
}
else
{
lean_object* v___x_3127_; 
lean_inc_ref(v_i_3110_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v_i_3110_);
v___x_3127_ = v___x_3116_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_i_3110_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
else
{
lean_object* v___x_3130_; 
lean_dec(v___x_3113_);
lean_dec(v_val_3112_);
lean_dec_ref(v_text_3105_);
v___x_3130_ = lean_box(0);
return v___x_3130_;
}
}
else
{
lean_object* v___x_3131_; 
lean_dec(v___x_3111_);
lean_dec_ref(v_text_3105_);
v___x_3131_ = lean_box(0);
return v___x_3131_;
}
}
else
{
lean_object* v___x_3132_; 
lean_dec_ref(v_text_3105_);
v___x_3132_ = lean_box(0);
return v___x_3132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object* v_text_3133_, lean_object* v_hoverLine_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_, lean_object* v_x_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_Widget_widgetInfosAt_x3f___lam__0(v_text_3133_, v_hoverLine_3134_, v_x_3135_, v_x_3136_, v_x_3137_);
lean_dec_ref(v_x_3137_);
lean_dec_ref(v_x_3136_);
lean_dec_ref(v_x_3135_);
lean_dec(v_hoverLine_3134_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object* v_text_3139_, lean_object* v_t_3140_, lean_object* v_hoverLine_3141_){
_start:
{
lean_object* v___f_3142_; lean_object* v___x_3143_; 
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_3142_, 0, v_text_3139_);
lean_closure_set(v___f_3142_, 1, v_hoverLine_3141_);
v___x_3143_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3142_, v_t_3140_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object* v_j_3144_, lean_object* v_k_3145_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = l_Lean_Json_getObjValD(v_j_3144_, v_k_3145_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object* v_j_3148_, lean_object* v_k_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_j_3148_, v_k_3149_);
lean_dec_ref(v_k_3149_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object* v_x_3153_){
_start:
{
if (lean_obj_tag(v_x_3153_) == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0));
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v_x_3153_);
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object* v_j_3157_, lean_object* v_k_3158_){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = l_Lean_Json_getObjValD(v_j_3157_, v_k_3158_);
v___x_3160_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(v___x_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object* v_j_3161_, lean_object* v_k_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_j_3161_, v_k_3162_);
lean_dec_ref(v_k_3162_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object* v_json_3168_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v_a_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v_a_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v_a_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3191_; 
v___x_3169_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_json_3168_);
v___x_3170_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3168_, v___x_3169_);
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___x_3170_);
v___x_3172_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_json_3168_);
v___x_3173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3168_, v___x_3172_);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_json_3168_);
v___x_3176_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3168_, v___x_3175_);
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_json_3168_);
v___x_3179_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3168_, v___x_3178_);
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3182_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3168_, v___x_3181_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3187_, 0, v_a_3171_);
lean_ctor_set(v___x_3187_, 1, v_a_3174_);
lean_ctor_set(v___x_3187_, 2, v_a_3177_);
lean_ctor_set(v___x_3187_, 3, v_a_3180_);
lean_ctor_set(v___x_3187_, 4, v_a_3183_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(lean_object* v_k_3194_, lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3195_) == 0)
{
lean_object* v___x_3196_; 
lean_dec_ref(v_k_3194_);
v___x_3196_ = lean_box(0);
return v___x_3196_;
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_val_3197_ = lean_ctor_get(v_x_3195_, 0);
lean_inc(v_val_3197_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_k_3194_);
lean_ctor_set(v___x_3198_, 1, v_val_3197_);
v___x_3199_ = lean_box(0);
v___x_3200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0___boxed(lean_object* v_k_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v_k_3201_, v_x_3202_);
lean_dec(v_x_3202_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(lean_object* v_x_3204_){
_start:
{
lean_object* v_id_3205_; lean_object* v_javascriptHash_3206_; lean_object* v_props_3207_; lean_object* v_range_x3f_3208_; lean_object* v_name_x3f_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_id_3205_ = lean_ctor_get(v_x_3204_, 0);
v_javascriptHash_3206_ = lean_ctor_get(v_x_3204_, 1);
v_props_3207_ = lean_ctor_get(v_x_3204_, 2);
v_range_x3f_3208_ = lean_ctor_get(v_x_3204_, 3);
v_name_x3f_3209_ = lean_ctor_get(v_x_3204_, 4);
v___x_3210_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_id_3205_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v_id_3205_);
v___x_3212_ = lean_box(0);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_javascriptHash_3206_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v_javascriptHash_3206_);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3212_);
v___x_3217_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_props_3207_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v_props_3207_);
v___x_3219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v___x_3212_);
v___x_3220_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3221_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v___x_3220_, v_range_x3f_3208_);
v___x_3222_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3223_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v___x_3222_, v_name_x3f_3209_);
v___x_3224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3212_);
v___x_3225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3221_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3219_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3216_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3213_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3230_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3228_, v___x_3229_);
v___x_3231_ = l_Lean_Json_mkObj(v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38____boxed(lean_object* v_x_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(v_x_3232_);
lean_dec_ref(v_x_3232_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_toWidgetInstance_3238_; lean_object* v_range_x3f_3239_; lean_object* v_name_x3f_3240_; lean_object* v_id_3241_; uint64_t v_javascriptHash_3242_; lean_object* v_props_3243_; lean_object* v___x_3244_; lean_object* v_fst_3245_; lean_object* v_snd_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3286_; 
v_toWidgetInstance_3238_ = lean_ctor_get(v_a_3236_, 0);
lean_inc_ref(v_toWidgetInstance_3238_);
v_range_x3f_3239_ = lean_ctor_get(v_a_3236_, 1);
lean_inc(v_range_x3f_3239_);
v_name_x3f_3240_ = lean_ctor_get(v_a_3236_, 2);
lean_inc(v_name_x3f_3240_);
lean_dec_ref(v_a_3236_);
v_id_3241_ = lean_ctor_get(v_toWidgetInstance_3238_, 0);
lean_inc(v_id_3241_);
v_javascriptHash_3242_ = lean_ctor_get_uint64(v_toWidgetInstance_3238_, sizeof(void*)*2);
v_props_3243_ = lean_ctor_get(v_toWidgetInstance_3238_, 1);
lean_inc_ref(v_props_3243_);
lean_dec_ref(v_toWidgetInstance_3238_);
v___x_3244_ = lean_apply_1(v_props_3243_, v_a_3237_);
v_fst_3245_ = lean_ctor_get(v___x_3244_, 0);
v_snd_3246_ = lean_ctor_get(v___x_3244_, 1);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3248_ = v___x_3244_;
v_isShared_3249_ = v_isSharedCheck_3286_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_snd_3246_);
lean_inc(v_fst_3245_);
lean_dec(v___x_3244_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3286_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
uint8_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___y_3256_; lean_object* v_fst_3257_; lean_object* v_snd_3258_; lean_object* v_fst_3265_; 
v___x_3250_ = 1;
v___x_3251_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3241_, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
v___x_3253_ = lean_uint64_to_nat(v_javascriptHash_3242_);
v___x_3254_ = l_Lean_bignumToJson(v___x_3253_);
if (lean_obj_tag(v_range_x3f_3239_) == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_box(0);
v_fst_3265_ = v___x_3276_;
goto v___jp_3264_;
}
else
{
lean_object* v_val_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3285_; 
v_val_3277_ = lean_ctor_get(v_range_x3f_3239_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_range_x3f_3239_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3279_ = v_range_x3f_3239_;
v_isShared_3280_ = v_isSharedCheck_3285_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_val_3277_);
lean_dec(v_range_x3f_3239_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3285_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_3277_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v___x_3281_);
v___x_3283_ = v___x_3279_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
v_fst_3265_ = v___x_3283_;
goto v___jp_3264_;
}
}
}
v___jp_3255_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3252_);
lean_ctor_set(v___x_3259_, 1, v___x_3254_);
lean_ctor_set(v___x_3259_, 2, v_fst_3245_);
lean_ctor_set(v___x_3259_, 3, v___y_3256_);
lean_ctor_set(v___x_3259_, 4, v_fst_3257_);
v___x_3260_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(v___x_3259_);
lean_dec_ref(v___x_3259_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 1, v_snd_3258_);
lean_ctor_set(v___x_3248_, 0, v___x_3260_);
v___x_3262_ = v___x_3248_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_snd_3258_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
v___jp_3264_:
{
if (lean_obj_tag(v_name_x3f_3240_) == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_box(0);
v___y_3256_ = v_fst_3265_;
v_fst_3257_ = v___x_3266_;
v_snd_3258_ = v_snd_3246_;
goto v___jp_3255_;
}
else
{
lean_object* v_val_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3275_; 
v_val_3267_ = lean_ctor_get(v_name_x3f_3240_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_name_x3f_3240_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3269_ = v_name_x3f_3240_;
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_val_3267_);
lean_dec(v_name_x3f_3240_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_val_3267_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3271_);
v___x_3273_ = v___x_3269_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
v___y_3256_ = v_fst_3265_;
v_fst_3257_ = v___x_3273_;
v_snd_3258_ = v_snd_3246_;
goto v___jp_3255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_props_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v_props_3287_);
lean_ctor_set(v___x_3289_, 1, v___y_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(v_j_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v_id_3301_; lean_object* v_javascriptHash_3302_; lean_object* v_props_3303_; lean_object* v_range_x3f_3304_; lean_object* v_name_x3f_3305_; lean_object* v___x_3306_; 
v_a_3300_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3300_);
lean_dec_ref(v___x_3291_);
v_id_3301_ = lean_ctor_get(v_a_3300_, 0);
lean_inc(v_id_3301_);
v_javascriptHash_3302_ = lean_ctor_get(v_a_3300_, 1);
lean_inc(v_javascriptHash_3302_);
v_props_3303_ = lean_ctor_get(v_a_3300_, 2);
lean_inc(v_props_3303_);
v_range_x3f_3304_ = lean_ctor_get(v_a_3300_, 3);
lean_inc(v_range_x3f_3304_);
v_name_x3f_3305_ = lean_ctor_get(v_a_3300_, 4);
lean_inc(v_name_x3f_3305_);
lean_dec(v_a_3300_);
v___x_3306_ = l_Lean_Name_fromJson_x3f(v_id_3301_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_name_x3f_3305_);
lean_dec(v_range_x3f_3304_);
lean_dec(v_props_3303_);
lean_dec(v_javascriptHash_3302_);
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3316_; 
v_a_3315_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3306_);
v___x_3316_ = l_UInt64_fromJson_x3f(v_javascriptHash_3302_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_a_3315_);
lean_dec(v_name_x3f_3305_);
lean_dec(v_range_x3f_3304_);
lean_dec(v_props_3303_);
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3379_; 
v_a_3325_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3327_ = v___x_3316_;
v_isShared_3328_ = v_isSharedCheck_3379_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3316_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3379_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___f_3329_; lean_object* v___y_3331_; lean_object* v_____do__lift_3332_; lean_object* v_____do__lift_3340_; 
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_), 2, 1);
lean_closure_set(v___f_3329_, 0, v_props_3303_);
if (lean_obj_tag(v_range_x3f_3304_) == 0)
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_box(0);
v_____do__lift_3340_ = v___x_3360_;
goto v___jp_3339_;
}
else
{
lean_object* v_val_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3378_; 
v_val_3361_ = lean_ctor_get(v_range_x3f_3304_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_range_x3f_3304_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3363_ = v_range_x3f_3304_;
v_isShared_3364_ = v_isSharedCheck_3378_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_val_3361_);
lean_dec(v_range_x3f_3304_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3378_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_3361_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_del_object(v___x_3363_);
lean_dec_ref(v___f_3329_);
lean_del_object(v___x_3327_);
lean_dec(v_a_3325_);
lean_dec(v_a_3315_);
lean_dec(v_name_x3f_3305_);
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; 
v_a_3374_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3365_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v_a_3374_);
v___x_3376_ = v___x_3363_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
v_____do__lift_3340_ = v___x_3376_;
goto v___jp_3339_;
}
}
}
}
v___jp_3330_:
{
lean_object* v___x_3333_; uint64_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3333_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3333_, 0, v_a_3315_);
lean_ctor_set(v___x_3333_, 1, v___f_3329_);
v___x_3334_ = lean_unbox_uint64(v_a_3325_);
lean_dec(v_a_3325_);
lean_ctor_set_uint64(v___x_3333_, sizeof(void*)*2, v___x_3334_);
v___x_3335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___y_3331_);
lean_ctor_set(v___x_3335_, 2, v_____do__lift_3332_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3335_);
v___x_3337_ = v___x_3327_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
v___jp_3339_:
{
if (lean_obj_tag(v_name_x3f_3305_) == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_box(0);
v___y_3331_ = v_____do__lift_3340_;
v_____do__lift_3332_ = v___x_3341_;
goto v___jp_3330_;
}
else
{
lean_object* v_val_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3359_; 
v_val_3342_ = lean_ctor_get(v_name_x3f_3305_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_name_x3f_3305_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3344_ = v_name_x3f_3305_;
v_isShared_3345_ = v_isSharedCheck_3359_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_val_3342_);
lean_dec(v_name_x3f_3305_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3359_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Json_getStr_x3f(v_val_3342_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_del_object(v___x_3344_);
lean_dec(v_____do__lift_3340_);
lean_dec_ref(v___f_3329_);
lean_del_object(v___x_3327_);
lean_dec(v_a_3325_);
lean_dec(v_a_3315_);
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; 
v_a_3355_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3355_);
lean_dec_ref(v___x_3346_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v_a_3355_);
v___x_3357_ = v___x_3344_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
v___y_3331_ = v_____do__lift_3340_;
v_____do__lift_3332_ = v___x_3357_;
goto v___jp_3330_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3380_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object* v_j_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3383_, v_a_3384_);
lean_dec_ref(v_a_3384_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object* v_json_3393_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v___x_3394_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3395_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3393_, v___x_3394_);
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(lean_object* v_x_3406_){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3407_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v_x_3406_);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___x_3409_);
v___x_3412_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3413_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3411_, v___x_3412_);
v___x_3414_ = l_Lean_Json_mkObj(v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t v_sz_3417_, size_t v_i_3418_, lean_object* v_bs_3419_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3418_, v_sz_3417_);
if (v___x_3420_ == 0)
{
return v_bs_3419_;
}
else
{
lean_object* v_v_3421_; lean_object* v___x_3422_; lean_object* v_bs_x27_3423_; size_t v___x_3424_; size_t v___x_3425_; lean_object* v___x_3426_; 
v_v_3421_ = lean_array_uget(v_bs_3419_, v_i_3418_);
v___x_3422_ = lean_unsigned_to_nat(0u);
v_bs_x27_3423_ = lean_array_uset(v_bs_3419_, v_i_3418_, v___x_3422_);
v___x_3424_ = ((size_t)1ULL);
v___x_3425_ = lean_usize_add(v_i_3418_, v___x_3424_);
v___x_3426_ = lean_array_uset(v_bs_x27_3423_, v_i_3418_, v_v_3421_);
v_i_3418_ = v___x_3425_;
v_bs_3419_ = v___x_3426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object* v_sz_3428_, lean_object* v_i_3429_, lean_object* v_bs_3430_){
_start:
{
size_t v_sz_boxed_3431_; size_t v_i_boxed_3432_; lean_object* v_res_3433_; 
v_sz_boxed_3431_ = lean_unbox_usize(v_sz_3428_);
lean_dec(v_sz_3428_);
v_i_boxed_3432_ = lean_unbox_usize(v_i_3429_);
lean_dec(v_i_3429_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_boxed_3431_, v_i_boxed_3432_, v_bs_3430_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object* v_a_3434_){
_start:
{
size_t v_sz_3435_; size_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_sz_3435_ = lean_array_size(v_a_3434_);
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3435_, v___x_3436_, v_a_3434_);
v___x_3438_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t v_sz_3439_, size_t v_i_3440_, lean_object* v_bs_3441_, lean_object* v___y_3442_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_lt(v_i_3440_, v_sz_3439_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v_bs_3441_);
lean_ctor_set(v___x_3444_, 1, v___y_3442_);
return v___x_3444_;
}
else
{
lean_object* v_v_3445_; lean_object* v___x_3446_; lean_object* v_fst_3447_; lean_object* v_snd_3448_; lean_object* v___x_3449_; lean_object* v_bs_x27_3450_; size_t v___x_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v_v_3445_ = lean_array_uget_borrowed(v_bs_3441_, v_i_3440_);
lean_inc(v_v_3445_);
v___x_3446_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3445_, v___y_3442_);
v_fst_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_fst_3447_);
v_snd_3448_ = lean_ctor_get(v___x_3446_, 1);
lean_inc(v_snd_3448_);
lean_dec_ref(v___x_3446_);
v___x_3449_ = lean_unsigned_to_nat(0u);
v_bs_x27_3450_ = lean_array_uset(v_bs_3441_, v_i_3440_, v___x_3449_);
v___x_3451_ = ((size_t)1ULL);
v___x_3452_ = lean_usize_add(v_i_3440_, v___x_3451_);
v___x_3453_ = lean_array_uset(v_bs_x27_3450_, v_i_3440_, v_fst_3447_);
v_i_3440_ = v___x_3452_;
v_bs_3441_ = v___x_3453_;
v___y_3442_ = v_snd_3448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object* v_sz_3455_, lean_object* v_i_3456_, lean_object* v_bs_3457_, lean_object* v___y_3458_){
_start:
{
size_t v_sz_boxed_3459_; size_t v_i_boxed_3460_; lean_object* v_res_3461_; 
v_sz_boxed_3459_ = lean_unbox_usize(v_sz_3455_);
lean_dec(v_sz_3455_);
v_i_boxed_3460_ = lean_unbox_usize(v_i_3456_);
lean_dec(v_i_3456_);
v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_boxed_3459_, v_i_boxed_3460_, v_bs_3457_, v___y_3458_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
size_t v_sz_3464_; size_t v___x_3465_; lean_object* v___x_3466_; lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3477_; 
v_sz_3464_ = lean_array_size(v_a_3462_);
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3464_, v___x_3465_, v_a_3462_, v_a_3463_);
v_fst_3467_ = lean_ctor_get(v___x_3466_, 0);
v_snd_3468_ = lean_ctor_get(v___x_3466_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3470_ = v___x_3466_;
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snd_3468_);
lean_inc(v_fst_3467_);
lean_dec(v___x_3466_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3472_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_fst_3467_);
v___x_3473_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(v___x_3472_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3473_);
v___x_3475_ = v___x_3470_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_snd_3468_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t v_sz_3478_, size_t v_i_3479_, lean_object* v_bs_3480_){
_start:
{
uint8_t v___x_3481_; 
v___x_3481_ = lean_usize_dec_lt(v_i_3479_, v_sz_3478_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_bs_3480_);
return v___x_3482_;
}
else
{
lean_object* v_v_3483_; lean_object* v___x_3484_; 
v_v_3483_ = lean_array_uget_borrowed(v_bs_3480_, v_i_3479_);
lean_inc(v_v_3483_);
v___x_3484_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3483_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v_bs_3480_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3484_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v_bs_x27_3495_; size_t v___x_3496_; size_t v___x_3497_; lean_object* v___x_3498_; 
v_a_3493_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3493_);
lean_dec_ref(v___x_3484_);
v___x_3494_ = lean_unsigned_to_nat(0u);
v_bs_x27_3495_ = lean_array_uset(v_bs_3480_, v_i_3479_, v___x_3494_);
v___x_3496_ = ((size_t)1ULL);
v___x_3497_ = lean_usize_add(v_i_3479_, v___x_3496_);
v___x_3498_ = lean_array_uset(v_bs_x27_3495_, v_i_3479_, v_a_3493_);
v_i_3479_ = v___x_3497_;
v_bs_3480_ = v___x_3498_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_bs_3502_){
_start:
{
size_t v_sz_boxed_3503_; size_t v_i_boxed_3504_; lean_object* v_res_3505_; 
v_sz_boxed_3503_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3504_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_boxed_3503_, v_i_boxed_3504_, v_bs_3502_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t v_sz_3506_, size_t v_i_3507_, lean_object* v_bs_3508_){
_start:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_usize_dec_lt(v_i_3507_, v_sz_3506_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_bs_3508_);
return v___x_3510_;
}
else
{
lean_object* v_v_3511_; lean_object* v___x_3512_; lean_object* v_bs_x27_3513_; size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v_v_3511_ = lean_array_uget(v_bs_3508_, v_i_3507_);
v___x_3512_ = lean_unsigned_to_nat(0u);
v_bs_x27_3513_ = lean_array_uset(v_bs_3508_, v_i_3507_, v___x_3512_);
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3507_, v___x_3514_);
v___x_3516_ = lean_array_uset(v_bs_x27_3513_, v_i_3507_, v_v_3511_);
v_i_3507_ = v___x_3515_;
v_bs_3508_ = v___x_3516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_sz_3518_, lean_object* v_i_3519_, lean_object* v_bs_3520_){
_start:
{
size_t v_sz_boxed_3521_; size_t v_i_boxed_3522_; lean_object* v_res_3523_; 
v_sz_boxed_3521_ = lean_unbox_usize(v_sz_3518_);
lean_dec(v_sz_3518_);
v_i_boxed_3522_ = lean_unbox_usize(v_i_3519_);
lean_dec(v_i_3519_);
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_3521_, v_i_boxed_3522_, v_bs_3520_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object* v_x_3525_){
_start:
{
if (lean_obj_tag(v_x_3525_) == 4)
{
lean_object* v_elems_3526_; size_t v_sz_3527_; size_t v___x_3528_; lean_object* v___x_3529_; 
v_elems_3526_ = lean_ctor_get(v_x_3525_, 0);
lean_inc_ref(v_elems_3526_);
lean_dec_ref(v_x_3525_);
v_sz_3527_ = lean_array_size(v_elems_3526_);
v___x_3528_ = ((size_t)0ULL);
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3527_, v___x_3528_, v_elems_3526_);
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3530_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0));
v___x_3531_ = lean_unsigned_to_nat(80u);
v___x_3532_ = l_Lean_Json_pretty(v_x_3525_, v___x_3531_);
v___x_3533_ = lean_string_append(v___x_3530_, v___x_3532_);
lean_dec_ref(v___x_3532_);
v___x_3534_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v___x_3535_ = lean_string_append(v___x_3533_, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
return v___x_3536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_j_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(v_j_3537_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3549_; 
v_a_3548_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3539_);
v___x_3549_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_a_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
else
{
lean_object* v_a_3558_; size_t v_sz_3559_; size_t v___x_3560_; lean_object* v___x_3561_; 
v_a_3558_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3549_);
v_sz_3559_ = lean_array_size(v_a_3558_);
v___x_3560_ = ((size_t)0ULL);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3559_, v___x_3560_, v_a_3558_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3561_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3561_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object* v_j_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_j_3578_, v_a_3579_);
lean_dec_ref(v_a_3579_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t v_sz_3581_, size_t v_i_3582_, lean_object* v_bs_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3581_, v_i_3582_, v_bs_3583_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object* v_sz_3586_, lean_object* v_i_3587_, lean_object* v_bs_3588_, lean_object* v___y_3589_){
_start:
{
size_t v_sz_boxed_3590_; size_t v_i_boxed_3591_; lean_object* v_res_3592_; 
v_sz_boxed_3590_ = lean_unbox_usize(v_sz_3586_);
lean_dec(v_sz_3586_);
v_i_boxed_3591_ = lean_unbox_usize(v_i_3587_);
lean_dec(v_i_3587_);
v_res_3592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_boxed_3590_, v_i_boxed_3591_, v_bs_3588_, v___y_3589_);
lean_dec_ref(v___y_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object* v_x_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
if (lean_obj_tag(v_x_3599_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3605_ = lean_ctor_get(v_x_3599_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v_x_3599_);
v___x_3606_ = l_Lean_stringToMessageData(v_a_3605_);
v___x_3607_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_3606_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
return v___x_3607_;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
v_a_3608_ = lean_ctor_get(v_x_3599_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_x_3599_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v_x_3599_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v_x_3599_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set_tag(v___x_3610_, 0);
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object* v_x_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object* v_id_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v_env_3630_; lean_object* v_options_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3629_ = lean_st_ref_get(v___y_3627_);
v_env_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc_ref(v_env_3630_);
lean_dec(v___x_3629_);
v_options_3631_ = lean_ctor_get(v___y_3626_, 2);
v___x_3632_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3633_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3630_, v_options_3631_, v___x_3632_, v_id_3623_);
v___x_3634_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v___x_3633_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object* v_id_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object* v___x_3642_, size_t v_sz_3643_, size_t v_i_3644_, lean_object* v_bs_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
uint8_t v___x_3651_; 
v___x_3651_ = lean_usize_dec_lt(v_i_3644_, v_sz_3643_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref(v___x_3642_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v_bs_3645_);
return v___x_3652_;
}
else
{
lean_object* v_v_3653_; lean_object* v_id_3654_; lean_object* v___x_3655_; lean_object* v_bs_x27_3656_; lean_object* v_a_3658_; lean_object* v___y_3668_; uint8_t v___x_3689_; lean_object* v___x_3690_; 
v_v_3653_ = lean_array_uget(v_bs_3645_, v_i_3644_);
v_id_3654_ = lean_ctor_get(v_v_3653_, 0);
v___x_3655_ = lean_unsigned_to_nat(0u);
v_bs_x27_3656_ = lean_array_uset(v_bs_3645_, v_i_3644_, v___x_3655_);
v___x_3689_ = 0;
lean_inc(v_id_3654_);
lean_inc_ref(v___x_3642_);
v___x_3690_ = l_Lean_Environment_find_x3f(v___x_3642_, v_id_3654_, v___x_3689_);
if (lean_obj_tag(v___x_3690_) == 0)
{
v___y_3668_ = v___x_3690_;
goto v___jp_3667_;
}
else
{
lean_object* v_val_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v_val_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_val_3691_);
v___x_3692_ = l_Lean_ConstantInfo_type(v_val_3691_);
lean_dec(v_val_3691_);
v___x_3693_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3694_ = l_Lean_Expr_isConstOf(v___x_3692_, v___x_3693_);
lean_dec_ref(v___x_3692_);
if (v___x_3694_ == 0)
{
lean_dec_ref(v___x_3690_);
goto v___jp_3665_;
}
else
{
v___y_3668_ = v___x_3690_;
goto v___jp_3667_;
}
}
v___jp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; size_t v___x_3661_; size_t v___x_3662_; lean_object* v___x_3663_; 
v___x_3659_ = lean_box(0);
v___x_3660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3660_, 0, v_v_3653_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
lean_ctor_set(v___x_3660_, 2, v_a_3658_);
v___x_3661_ = ((size_t)1ULL);
v___x_3662_ = lean_usize_add(v_i_3644_, v___x_3661_);
v___x_3663_ = lean_array_uset(v_bs_x27_3656_, v_i_3644_, v___x_3660_);
v_i_3644_ = v___x_3662_;
v_bs_3645_ = v___x_3663_;
goto _start;
}
v___jp_3665_:
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_box(0);
v_a_3658_ = v___x_3666_;
goto v___jp_3657_;
}
v___jp_3667_:
{
if (lean_obj_tag(v___y_3668_) == 0)
{
goto v___jp_3665_;
}
else
{
lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3687_; 
v_isSharedCheck_3687_ = !lean_is_exclusive(v___y_3668_);
if (v_isSharedCheck_3687_ == 0)
{
lean_object* v_unused_3688_; 
v_unused_3688_ = lean_ctor_get(v___y_3668_, 0);
lean_dec(v_unused_3688_);
v___x_3670_ = v___y_3668_;
v_isShared_3671_ = v_isSharedCheck_3687_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v___y_3668_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3687_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v_id_3672_; lean_object* v___x_3673_; 
v_id_3672_ = lean_ctor_get(v_v_3653_, 0);
lean_inc(v_id_3672_);
v___x_3673_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3672_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v_name_3675_; lean_object* v___x_3677_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v_name_3675_ = lean_ctor_get(v_a_3674_, 0);
lean_inc_ref(v_name_3675_);
lean_dec(v_a_3674_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_name_3675_);
v___x_3677_ = v___x_3670_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_name_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
v_a_3658_ = v___x_3677_;
goto v___jp_3657_;
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_del_object(v___x_3670_);
lean_dec_ref(v_bs_x27_3656_);
lean_dec(v_v_3653_);
lean_dec_ref(v___x_3642_);
v_a_3679_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3673_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3673_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object* v___x_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_bs_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
size_t v_sz_boxed_3704_; size_t v_i_boxed_3705_; lean_object* v_res_3706_; 
v_sz_boxed_3704_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3705_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3695_, v_sz_boxed_3704_, v_i_boxed_3705_, v_bs_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object* v___x_3707_, lean_object* v___x_3708_, size_t v_sz_3709_, size_t v_i_3710_, lean_object* v_bs_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_usize_dec_lt(v_i_3710_, v_sz_3709_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; 
lean_dec_ref(v___x_3708_);
lean_dec_ref(v___x_3707_);
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v_bs_3711_);
return v___x_3718_;
}
else
{
lean_object* v_v_3719_; lean_object* v_toWidgetInstance_3720_; lean_object* v_stx_3721_; lean_object* v_id_3722_; lean_object* v___x_3723_; lean_object* v_bs_x27_3724_; lean_object* v___y_3726_; lean_object* v___y_3727_; uint8_t v___x_3733_; lean_object* v_a_3735_; lean_object* v___y_3750_; lean_object* v___x_3770_; 
v_v_3719_ = lean_array_uget_borrowed(v_bs_3711_, v_i_3710_);
v_toWidgetInstance_3720_ = lean_ctor_get(v_v_3719_, 0);
lean_inc_ref(v_toWidgetInstance_3720_);
v_stx_3721_ = lean_ctor_get(v_v_3719_, 1);
lean_inc(v_stx_3721_);
v_id_3722_ = lean_ctor_get(v_toWidgetInstance_3720_, 0);
v___x_3723_ = lean_unsigned_to_nat(0u);
v_bs_x27_3724_ = lean_array_uset(v_bs_3711_, v_i_3710_, v___x_3723_);
v___x_3733_ = 0;
lean_inc(v_id_3722_);
lean_inc_ref(v___x_3708_);
v___x_3770_ = l_Lean_Environment_find_x3f(v___x_3708_, v_id_3722_, v___x_3733_);
if (lean_obj_tag(v___x_3770_) == 0)
{
v___y_3750_ = v___x_3770_;
goto v___jp_3749_;
}
else
{
lean_object* v_val_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
v_val_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_val_3771_);
v___x_3772_ = l_Lean_ConstantInfo_type(v_val_3771_);
lean_dec(v_val_3771_);
v___x_3773_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3774_ = l_Lean_Expr_isConstOf(v___x_3772_, v___x_3773_);
lean_dec_ref(v___x_3772_);
if (v___x_3774_ == 0)
{
lean_dec_ref(v___x_3770_);
goto v___jp_3747_;
}
else
{
v___y_3750_ = v___x_3770_;
goto v___jp_3749_;
}
}
v___jp_3725_:
{
lean_object* v___x_3728_; size_t v___x_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3728_, 0, v_toWidgetInstance_3720_);
lean_ctor_set(v___x_3728_, 1, v___y_3727_);
lean_ctor_set(v___x_3728_, 2, v___y_3726_);
v___x_3729_ = ((size_t)1ULL);
v___x_3730_ = lean_usize_add(v_i_3710_, v___x_3729_);
v___x_3731_ = lean_array_uset(v_bs_x27_3724_, v_i_3710_, v___x_3728_);
v_i_3710_ = v___x_3730_;
v_bs_3711_ = v___x_3731_;
goto _start;
}
v___jp_3734_:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Syntax_getRange_x3f(v_stx_3721_, v___x_3733_);
lean_dec(v_stx_3721_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_box(0);
v___y_3726_ = v_a_3735_;
v___y_3727_ = v___x_3737_;
goto v___jp_3725_;
}
else
{
lean_object* v_val_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3746_; 
v_val_3738_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3740_ = v___x_3736_;
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_val_3738_);
lean_dec(v___x_3736_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_inc_ref(v___x_3707_);
v___x_3742_ = l_Lean_Syntax_Range_toLspRange(v___x_3707_, v_val_3738_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3742_);
v___x_3744_ = v___x_3740_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
v___y_3726_ = v_a_3735_;
v___y_3727_ = v___x_3744_;
goto v___jp_3725_;
}
}
}
}
v___jp_3747_:
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_box(0);
v_a_3735_ = v___x_3748_;
goto v___jp_3734_;
}
v___jp_3749_:
{
if (lean_obj_tag(v___y_3750_) == 0)
{
goto v___jp_3747_;
}
else
{
lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3768_; 
v_isSharedCheck_3768_ = !lean_is_exclusive(v___y_3750_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___y_3750_, 0);
lean_dec(v_unused_3769_);
v___x_3752_ = v___y_3750_;
v_isShared_3753_ = v_isSharedCheck_3768_;
goto v_resetjp_3751_;
}
else
{
lean_dec(v___y_3750_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3768_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; 
lean_inc(v_id_3722_);
v___x_3754_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3722_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v_name_3756_; lean_object* v___x_3758_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref(v___x_3754_);
v_name_3756_ = lean_ctor_get(v_a_3755_, 0);
lean_inc_ref(v_name_3756_);
lean_dec(v_a_3755_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v_name_3756_);
v___x_3758_ = v___x_3752_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_name_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
v_a_3735_ = v___x_3758_;
goto v___jp_3734_;
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_del_object(v___x_3752_);
lean_dec_ref(v_bs_x27_3724_);
lean_dec(v_stx_3721_);
lean_dec_ref(v_toWidgetInstance_3720_);
lean_dec_ref(v___x_3708_);
lean_dec_ref(v___x_3707_);
v_a_3760_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3754_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3754_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object* v___x_3775_, lean_object* v___x_3776_, lean_object* v_sz_3777_, lean_object* v_i_3778_, lean_object* v_bs_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
size_t v_sz_boxed_3785_; size_t v_i_boxed_3786_; lean_object* v_res_3787_; 
v_sz_boxed_3785_ = lean_unbox_usize(v_sz_3777_);
lean_dec(v_sz_3777_);
v_i_boxed_3786_ = lean_unbox_usize(v_i_3778_);
lean_dec(v_i_3778_);
v_res_3787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3775_, v___x_3776_, v_sz_boxed_3785_, v_i_boxed_3786_, v_bs_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object* v_pos_3788_, lean_object* v_text_3789_, lean_object* v_val_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = lean_st_ref_get(v___y_3794_);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
v___x_3797_ = l_Lean_Widget_evalPanelWidgets(v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v_env_3799_; size_t v_sz_3800_; size_t v___x_3801_; lean_object* v___x_3802_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
v_env_3799_ = lean_ctor_get(v___x_3796_, 0);
lean_inc_ref(v_env_3799_);
lean_dec(v___x_3796_);
v_sz_3800_ = lean_array_size(v_a_3798_);
v___x_3801_ = ((size_t)0ULL);
lean_inc_ref(v_env_3799_);
v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v_env_3799_, v_sz_3800_, v___x_3801_, v_a_3798_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v_line_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; size_t v_sz_3807_; lean_object* v___x_3808_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref(v___x_3802_);
v_line_3804_ = lean_ctor_get(v_pos_3788_, 0);
lean_inc(v_line_3804_);
lean_dec_ref(v_pos_3788_);
lean_inc_ref(v_text_3789_);
v___x_3805_ = l_Lean_Widget_widgetInfosAt_x3f(v_text_3789_, v_val_3790_, v_line_3804_);
v___x_3806_ = lean_array_mk(v___x_3805_);
v_sz_3807_ = lean_array_size(v___x_3806_);
v___x_3808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v_text_3789_, v_env_3799_, v_sz_3807_, v___x_3801_, v___x_3806_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3817_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3817_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3817_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = l_Array_append___redArg(v_a_3803_, v_a_3809_);
lean_dec(v_a_3809_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3813_);
v___x_3815_ = v___x_3811_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_a_3803_);
v_a_3818_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3808_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3808_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_env_3799_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_val_3790_);
lean_dec_ref(v_text_3789_);
lean_dec_ref(v_pos_3788_);
v_a_3826_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3802_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3802_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v___x_3796_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_val_3790_);
lean_dec_ref(v_text_3789_);
lean_dec_ref(v_pos_3788_);
v_a_3834_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3797_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3797_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object* v_pos_3842_, lean_object* v_text_3843_, lean_object* v_val_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3842_, v_text_3843_, v_val_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object* v_pos_3855_, lean_object* v_text_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_){
_start:
{
if (lean_obj_tag(v_x_3857_) == 1)
{
lean_object* v_val_3863_; 
v_val_3863_ = lean_ctor_get(v_x_3857_, 0);
lean_inc(v_val_3863_);
lean_dec_ref(v_x_3857_);
if (lean_obj_tag(v_val_3863_) == 0)
{
lean_object* v_i_3864_; 
v_i_3864_ = lean_ctor_get(v_val_3863_, 0);
if (lean_obj_tag(v_i_3864_) == 0)
{
lean_object* v_info_3865_; lean_object* v___f_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_info_3865_ = lean_ctor_get(v_i_3864_, 0);
lean_inc_ref(v_info_3865_);
v___f_3866_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3866_, 0, v_pos_3855_);
lean_closure_set(v___f_3866_, 1, v_text_3856_);
lean_closure_set(v___f_3866_, 2, v_val_3863_);
v___x_3867_ = lean_box(0);
v___x_3868_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__1));
v___x_3869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3869_, 0, v_info_3865_);
lean_ctor_set(v___x_3869_, 1, v___x_3867_);
lean_ctor_set(v___x_3869_, 2, v___x_3868_);
v___x_3870_ = lean_obj_once(&l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l_Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_3871_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_3869_, v___x_3870_, v___f_3866_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3888_; 
v_a_3880_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3882_ = v___x_3871_;
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3871_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = l_Lean_Server_RequestError_ofIoError(v_a_3880_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3884_);
v___x_3886_ = v___x_3882_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
else
{
lean_dec_ref(v_val_3863_);
lean_dec_ref(v_text_3856_);
lean_dec_ref(v_pos_3855_);
goto v___jp_3860_;
}
}
else
{
lean_dec(v_val_3863_);
lean_dec_ref(v_text_3856_);
lean_dec_ref(v_pos_3855_);
goto v___jp_3860_;
}
}
else
{
lean_dec(v_x_3857_);
lean_dec_ref(v_text_3856_);
lean_dec_ref(v_pos_3855_);
goto v___jp_3860_;
}
v___jp_3860_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__0));
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object* v_pos_3889_, lean_object* v_text_3890_, lean_object* v_x_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3889_, v_text_3890_, v_x_3891_, v___y_3892_);
lean_dec_ref(v___y_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets(lean_object* v_pos_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v___x_3898_; lean_object* v_a_3899_; lean_object* v_toEditableDocumentCore_3900_; lean_object* v_meta_3901_; lean_object* v_text_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3898_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_3896_);
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v_toEditableDocumentCore_3900_ = lean_ctor_get(v_a_3899_, 0);
v_meta_3901_ = lean_ctor_get(v_toEditableDocumentCore_3900_, 0);
v_text_3902_ = lean_ctor_get(v_meta_3901_, 3);
lean_inc_ref(v_text_3902_);
lean_inc_ref(v_pos_3895_);
v___f_3903_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3903_, 0, v_pos_3895_);
lean_closure_set(v___f_3903_, 1, v_text_3902_);
v___x_3904_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3902_, v_pos_3895_);
v___x_3905_ = 1;
v___x_3906_ = l_Lean_Server_RequestM_findInfoTreeAtPos(v_a_3899_, v___x_3904_, v___x_3905_);
v___x_3907_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3906_, v___f_3903_, v_a_3896_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object* v_pos_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Widget_getWidgets(v_pos_3908_, v_a_3909_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object* v_00_u03b1_3912_, lean_object* v_x_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3920_, lean_object* v_x_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(v_00_u03b1_3920_, v_x_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object* v_val_3928_, lean_object* v___f_3929_, lean_object* v_x_3930_, lean_object* v___y_3931_){
_start:
{
if (lean_obj_tag(v_x_3930_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v___f_3929_);
v_a_3933_ = lean_ctor_get(v_x_3930_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_x_3930_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v_x_3930_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v_x_3930_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
lean_ctor_set_tag(v___x_3935_, 1);
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3957_; 
v_a_3941_ = lean_ctor_get(v_x_3930_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_x_3930_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3943_ = v_x_3930_;
v_isShared_3944_ = v_isSharedCheck_3957_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v_x_3930_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3957_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; lean_object* v_objects_3946_; lean_object* v_expireTime_3947_; lean_object* v___f_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v_fst_3951_; lean_object* v_snd_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3945_ = lean_st_ref_take(v_val_3928_);
v_objects_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc_ref(v_objects_3946_);
v_expireTime_3947_ = lean_ctor_get(v___x_3945_, 1);
lean_inc(v_expireTime_3947_);
lean_dec(v___x_3945_);
v___f_3948_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_3948_, 0, v_expireTime_3947_);
v___x_3949_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_a_3941_, v_objects_3946_);
v___x_3950_ = l_Prod_map___redArg(v___f_3929_, v___f_3948_, v___x_3949_);
v_fst_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_fst_3951_);
v_snd_3952_ = lean_ctor_get(v___x_3950_, 1);
lean_inc(v_snd_3952_);
lean_dec_ref(v___x_3950_);
v___x_3953_ = lean_st_ref_set(v_val_3928_, v_snd_3952_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set_tag(v___x_3943_, 0);
lean_ctor_set(v___x_3943_, 0, v_fst_3951_);
v___x_3955_ = v___x_3943_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_fst_3951_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object* v_val_3958_, lean_object* v___f_3959_, lean_object* v_x_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_3958_, v___f_3959_, v_x_3960_, v___y_3961_);
lean_dec_ref(v___y_3961_);
lean_dec(v_val_3958_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object* v_method_3964_, lean_object* v_handler_3965_, lean_object* v___f_3966_, uint64_t v_seshId_3967_, lean_object* v_j_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_rpcSessions_3971_; lean_object* v___x_3972_; 
v_rpcSessions_3971_ = lean_ctor_get(v___y_3969_, 0);
v___x_3972_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_3971_, v_seshId_3967_);
if (lean_obj_tag(v___x_3972_) == 1)
{
lean_object* v_val_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_val_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_val_3973_);
lean_dec_ref(v___x_3972_);
v___x_3974_ = lean_st_ref_get(v_val_3973_);
lean_dec(v___x_3974_);
lean_inc(v_j_3968_);
v___x_3975_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v_j_3968_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3996_; 
lean_dec(v_val_3973_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v___f_3966_);
lean_dec_ref(v_handler_3965_);
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3996_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3996_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
uint8_t v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3980_ = 3;
v___x_3981_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_3982_ = 1;
v___x_3983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_3964_, v___x_3982_);
v___x_3984_ = lean_string_append(v___x_3981_, v___x_3983_);
lean_dec_ref(v___x_3983_);
v___x_3985_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_3986_ = lean_string_append(v___x_3984_, v___x_3985_);
v___x_3987_ = l_Lean_Json_compress(v_j_3968_);
v___x_3988_ = lean_string_append(v___x_3986_, v___x_3987_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_3990_ = lean_string_append(v___x_3988_, v___x_3989_);
v___x_3991_ = lean_string_append(v___x_3990_, v_a_3976_);
lean_dec(v_a_3976_);
v___x_3992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*1, v___x_3980_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set_tag(v___x_3978_, 1);
lean_ctor_set(v___x_3978_, 0, v___x_3992_);
v___x_3994_ = v___x_3978_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3998_; 
lean_dec(v_j_3968_);
lean_dec(v_method_3964_);
v_a_3997_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3997_);
lean_dec_ref(v___x_3975_);
lean_inc_ref(v___y_3969_);
v___x_3998_ = lean_apply_3(v_handler_3965_, v_a_3997_, v___y_3969_, lean_box(0));
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___f_4000_; lean_object* v___x_4001_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___f_4000_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4000_, 0, v_val_3973_);
lean_closure_set(v___f_4000_, 1, v___f_3966_);
v___x_4001_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_3999_, v___f_4000_, v___y_3969_);
return v___x_4001_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v_val_3973_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v___f_3966_);
v_a_4002_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3998_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3998_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec(v___x_3972_);
lean_dec_ref(v___y_3969_);
lean_dec(v_j_3968_);
lean_dec_ref(v___f_3966_);
lean_dec_ref(v_handler_3965_);
lean_dec(v_method_3964_);
v___x_4010_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_method_4012_, lean_object* v_handler_4013_, lean_object* v___f_4014_, lean_object* v_seshId_4015_, lean_object* v_j_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
uint64_t v_seshId_boxed_4019_; lean_object* v_res_4020_; 
v_seshId_boxed_4019_ = lean_unbox_uint64(v_seshId_4015_);
lean_dec_ref(v_seshId_4015_);
v_res_4020_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_method_4012_, v_handler_4013_, v___f_4014_, v_seshId_boxed_4019_, v_j_4016_, v___y_4017_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_4021_, lean_object* v_handler_4022_){
_start:
{
lean_object* v___f_4023_; lean_object* v___f_4024_; 
v___f_4023_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_4024_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4024_, 0, v_method_4021_);
lean_closure_set(v___f_4024_, 1, v_handler_4022_);
lean_closure_set(v___f_4024_, 2, v___f_4023_);
return v___f_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object* v_method_4025_, lean_object* v_handler_4026_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4062_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4062_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4062_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; uint8_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v_errMsg_4038_; uint8_t v___x_4039_; 
v___x_4033_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_4034_ = 1;
lean_inc(v_method_4025_);
v___x_4035_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_4025_, v___x_4034_);
v___x_4036_ = lean_string_append(v___x_4033_, v___x_4035_);
lean_dec_ref(v___x_4035_);
v___x_4037_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_4038_ = lean_string_append(v___x_4036_, v___x_4037_);
v___x_4039_ = lean_unbox(v_a_4029_);
lean_dec(v_a_4029_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
lean_dec_ref(v_handler_4026_);
lean_dec(v_method_4025_);
v___x_4040_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_4041_ = lean_string_append(v_errMsg_4038_, v___x_4040_);
v___x_4042_ = lean_mk_io_user_error(v___x_4041_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set_tag(v___x_4031_, 1);
lean_ctor_set(v___x_4031_, 0, v___x_4042_);
v___x_4044_ = v___x_4031_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; 
v___x_4046_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_4047_ = lean_st_ref_get(v___x_4046_);
v___x_4048_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4047_, v_method_4025_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
lean_dec_ref(v_errMsg_4038_);
v___x_4049_ = lean_st_ref_take(v___x_4046_);
lean_inc(v_method_4025_);
v___x_4050_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(v_method_4025_, v_handler_4026_);
v___x_4051_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4049_, v_method_4025_, v___x_4050_);
v___x_4052_ = lean_st_ref_set(v___x_4046_, v___x_4051_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4052_);
v___x_4054_ = v___x_4031_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
lean_dec_ref(v_handler_4026_);
lean_dec(v_method_4025_);
v___x_4056_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_4057_ = lean_string_append(v_errMsg_4038_, v___x_4056_);
v___x_4058_ = lean_mk_io_user_error(v___x_4057_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set_tag(v___x_4031_, 1);
lean_ctor_set(v___x_4031_, 0, v___x_4058_);
v___x_4060_ = v___x_4031_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec_ref(v_handler_4026_);
lean_dec(v_method_4025_);
v_a_4063_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4028_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4028_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4071_, lean_object* v_handler_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_4071_, v_handler_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4083_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4084_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v___x_4082_, v___x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
return v_res_4086_;
}
}
lean_object* runtime_initialize_Lean_Elab_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_RequestHandling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef);
lean_dec_ref(res);
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry);
lean_dec_ref(res);
res = l_Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Widget_widgetModuleAttrImpl = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Widget_widgetModuleAttrImpl);
lean_dec_ref(res);
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt);
lean_dec_ref(res);
l_Lean_Widget_instInhabitedUserWidgetDefinition_default = _init_l_Lean_Widget_instInhabitedUserWidgetDefinition_default();
lean_mark_persistent(l_Lean_Widget_instInhabitedUserWidgetDefinition_default);
l_Lean_Widget_instInhabitedUserWidgetDefinition = _init_l_Lean_Widget_instInhabitedUserWidgetDefinition();
lean_mark_persistent(l_Lean_Widget_instInhabitedUserWidgetDefinition);
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Widget_UserWidget(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin);
lean_object* initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_RequestHandling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Widget_UserWidget(builtin);
}
#ifdef __cplusplus
}
#endif
