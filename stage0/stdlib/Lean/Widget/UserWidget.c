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
lean_object* l_Lean_UInt64_fromJson_x3f(lean_object*);
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
lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
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
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "addBuiltinModule"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "A widget module with the same hash(JS source code) was already registered at "};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToModule"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toModule"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "A builtin widget module with the same hash(JS source code) was already registered."};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "widgetModuleAttrImpl"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 203, 59, 214, 15, 221, 203, 217)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "Registers a widget module. Its type must implement Lean.Widget.ToModule."};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_widget_module"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 42, 123, 194, 197, 140, 191, 110)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "widget_module"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 72, 138, 198, 227, 75, 129, 42)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedWidgetSource_default = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedWidgetSource = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value)}};
static const lean_object* l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0 = (const lean_object*)&l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedUserWidgetDefinition_default = (const lean_object*)&l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedUserWidgetDefinition = (const lean_object*)&l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_value;
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object*);
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
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
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
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
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
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_516_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_523_, lean_object* v___y_524_, lean_object* v___y_525_){
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
v___x_538_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2);
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
v___x_550_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(v_env_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec(v___y_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1(lean_object* v_env_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(v_env_568_, v___y_570_, v___y_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1(v_env_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_582_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_ctor_set(v___x_587_, 2, v___x_586_);
lean_ctor_set(v___x_587_, 3, v___x_586_);
lean_ctor_set(v___x_587_, 4, v___x_585_);
lean_ctor_set(v___x_587_, 5, v___x_585_);
lean_ctor_set(v___x_587_, 6, v___x_585_);
lean_ctor_set(v___x_587_, 7, v___x_585_);
lean_ctor_set(v___x_587_, 8, v___x_585_);
lean_ctor_set(v___x_587_, 9, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_591_ = ((size_t)5ULL);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_unsigned_to_nat(32u);
v___x_594_ = lean_mk_empty_array_with_capacity(v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_596_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___x_592_);
lean_ctor_set(v___x_596_, 3, v___x_592_);
lean_ctor_set_usize(v___x_596_, 4, v___x_591_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_box(1);
v___x_598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v_options_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
v_options_607_ = lean_ctor_get(v___y_602_, 2);
v___x_608_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__5);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(v_msgData_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_ref_622_; lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_ref_622_ = lean_ctor_get(v___y_619_, 5);
v___x_623_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0(v_msg_618_, v___y_619_, v___y_620_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v_msg_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_637_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v_name_644_, lean_object* v_decl_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_650_ = l_Lean_MessageData_ofName(v_name_644_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v___x_653_, v___y_646_, v___y_647_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_name_655_, lean_object* v_decl_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v_name_655_, v_decl_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_decl_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_msgData_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v_env_668_; lean_object* v___x_669_; lean_object* v_mctx_670_; lean_object* v_lctx_671_; lean_object* v_options_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_667_ = lean_st_ref_get(v___y_665_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref(v_env_668_);
lean_dec(v___x_667_);
v___x_669_ = lean_st_ref_get(v___y_663_);
v_mctx_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_mctx_670_);
lean_dec(v___x_669_);
v_lctx_671_ = lean_ctor_get(v___y_662_, 2);
v_options_672_ = lean_ctor_get(v___y_664_, 2);
lean_inc_ref(v_options_672_);
lean_inc_ref(v_lctx_671_);
v___x_673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_673_, 0, v_env_668_);
lean_ctor_set(v___x_673_, 1, v_mctx_670_);
lean_ctor_set(v___x_673_, 2, v_lctx_671_);
lean_ctor_set(v___x_673_, 3, v_options_672_);
v___x_674_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_msgData_661_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msgData_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_ref_689_; lean_object* v___x_690_; lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_ref_689_ = lean_ctor_get(v___y_686_, 5);
v___x_690_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msg_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_inc(v_ref_689_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_ref_689_);
lean_ctor_set(v___x_695_, 1, v_a_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 1);
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_706_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_719_, uint8_t v_kind_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___y_732_; 
v___x_726_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_727_ = l_Lean_MessageData_ofName(v_name_719_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
switch(v_kind_720_)
{
case 0:
{
lean_object* v___x_739_; 
v___x_739_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_732_ = v___x_739_;
goto v___jp_731_;
}
case 1:
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_732_ = v___x_740_;
goto v___jp_731_;
}
default: 
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_732_ = v___x_741_;
goto v___jp_731_;
}
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_inc_ref(v___y_732_);
v___x_733_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_733_, 0, v___y_732_);
v___x_734_ = l_Lean_MessageData_ofFormat(v___x_733_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_730_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_737_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_742_, lean_object* v_kind_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
uint8_t v_kind_boxed_749_; lean_object* v_res_750_; 
v_kind_boxed_749_ = lean_unbox(v_kind_743_);
v_res_750_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_742_, v_kind_boxed_749_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_750_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_opts_751_, lean_object* v_opt_752_){
_start:
{
lean_object* v_name_753_; lean_object* v_defValue_754_; lean_object* v_map_755_; lean_object* v___x_756_; 
v_name_753_ = lean_ctor_get(v_opt_752_, 0);
v_defValue_754_ = lean_ctor_get(v_opt_752_, 1);
v_map_755_ = lean_ctor_get(v_opts_751_, 0);
v___x_756_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_755_, v_name_753_);
if (lean_obj_tag(v___x_756_) == 0)
{
uint8_t v___x_757_; 
v___x_757_ = lean_unbox(v_defValue_754_);
return v___x_757_;
}
else
{
lean_object* v_val_758_; 
v_val_758_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v___x_756_, 1);
if (lean_obj_tag(v_val_758_) == 1)
{
uint8_t v_v_759_; 
v_v_759_ = lean_ctor_get_uint8(v_val_758_, 0);
lean_dec_ref_known(v_val_758_, 0);
return v_v_759_;
}
else
{
uint8_t v___x_760_; 
lean_dec(v_val_758_);
v___x_760_ = lean_unbox(v_defValue_754_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_opts_761_, lean_object* v_opt_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_opts_761_, v_opt_762_);
lean_dec_ref(v_opt_762_);
lean_dec_ref(v_opts_761_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t v___y_773_, uint8_t v_suppressElabErrors_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 1)
{
lean_object* v_pre_776_; 
v_pre_776_ = lean_ctor_get(v_x_775_, 0);
switch(lean_obj_tag(v_pre_776_))
{
case 1:
{
lean_object* v_pre_777_; 
v_pre_777_ = lean_ctor_get(v_pre_776_, 0);
switch(lean_obj_tag(v_pre_777_))
{
case 0:
{
lean_object* v_str_778_; lean_object* v_str_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_str_778_ = lean_ctor_get(v_x_775_, 1);
v_str_779_ = lean_ctor_get(v_pre_776_, 1);
v___x_780_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_781_ = lean_string_dec_eq(v_str_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_783_ = lean_string_dec_eq(v_str_779_, v___x_782_);
if (v___x_783_ == 0)
{
return v___y_773_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_785_ = lean_string_dec_eq(v_str_778_, v___x_784_);
if (v___x_785_ == 0)
{
return v___y_773_;
}
else
{
return v_suppressElabErrors_774_;
}
}
}
else
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_787_ = lean_string_dec_eq(v_str_778_, v___x_786_);
if (v___x_787_ == 0)
{
return v___y_773_;
}
else
{
return v_suppressElabErrors_774_;
}
}
}
case 1:
{
lean_object* v_pre_788_; 
v_pre_788_ = lean_ctor_get(v_pre_777_, 0);
if (lean_obj_tag(v_pre_788_) == 0)
{
lean_object* v_str_789_; lean_object* v_str_790_; lean_object* v_str_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_str_789_ = lean_ctor_get(v_x_775_, 1);
v_str_790_ = lean_ctor_get(v_pre_776_, 1);
v_str_791_ = lean_ctor_get(v_pre_777_, 1);
v___x_792_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_793_ = lean_string_dec_eq(v_str_791_, v___x_792_);
if (v___x_793_ == 0)
{
return v___y_773_;
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_795_ = lean_string_dec_eq(v_str_790_, v___x_794_);
if (v___x_795_ == 0)
{
return v___y_773_;
}
else
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6));
v___x_797_ = lean_string_dec_eq(v_str_789_, v___x_796_);
if (v___x_797_ == 0)
{
return v___y_773_;
}
else
{
return v_suppressElabErrors_774_;
}
}
}
}
else
{
return v___y_773_;
}
}
default: 
{
return v___y_773_;
}
}
}
case 0:
{
lean_object* v_str_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_str_798_ = lean_ctor_get(v_x_775_, 1);
v___x_799_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7));
v___x_800_ = lean_string_dec_eq(v_str_798_, v___x_799_);
if (v___x_800_ == 0)
{
return v___y_773_;
}
else
{
return v_suppressElabErrors_774_;
}
}
default: 
{
return v___y_773_;
}
}
}
else
{
return v___y_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___y_801_, lean_object* v_suppressElabErrors_802_, lean_object* v_x_803_){
_start:
{
uint8_t v___y_10927__boxed_804_; uint8_t v_suppressElabErrors_boxed_805_; uint8_t v_res_806_; lean_object* v_r_807_; 
v___y_10927__boxed_804_ = lean_unbox(v___y_801_);
v_suppressElabErrors_boxed_805_ = lean_unbox(v_suppressElabErrors_802_);
v_res_806_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v___y_10927__boxed_804_, v_suppressElabErrors_boxed_805_, v_x_803_);
lean_dec(v_x_803_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_ref_809_, lean_object* v_msgData_810_, uint8_t v_severity_811_, uint8_t v_isSilent_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_855_; uint8_t v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_859_; uint8_t v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_880_; uint8_t v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; uint8_t v___y_884_; lean_object* v___y_885_; uint8_t v___y_886_; lean_object* v___y_887_; lean_object* v___y_891_; uint8_t v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; uint8_t v___x_902_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; uint8_t v___y_907_; lean_object* v___y_908_; uint8_t v___y_909_; uint8_t v___y_910_; uint8_t v___y_912_; uint8_t v___x_927_; 
v___x_902_ = 2;
v___x_927_ = l_Lean_instBEqMessageSeverity_beq(v_severity_811_, v___x_902_);
if (v___x_927_ == 0)
{
v___y_912_ = v___x_927_;
goto v___jp_911_;
}
else
{
uint8_t v___x_928_; 
lean_inc_ref(v_msgData_810_);
v___x_928_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_810_);
v___y_912_ = v___x_928_;
goto v___jp_911_;
}
v___jp_818_:
{
lean_object* v___x_828_; lean_object* v_currNamespace_829_; lean_object* v_openDecls_830_; lean_object* v_env_831_; lean_object* v_nextMacroScope_832_; lean_object* v_ngen_833_; lean_object* v_auxDeclNGen_834_; lean_object* v_traceState_835_; lean_object* v_cache_836_; lean_object* v_messages_837_; lean_object* v_infoState_838_; lean_object* v_snapshotTasks_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_853_; 
v___x_828_ = lean_st_ref_take(v___y_827_);
v_currNamespace_829_ = lean_ctor_get(v___y_826_, 6);
v_openDecls_830_ = lean_ctor_get(v___y_826_, 7);
v_env_831_ = lean_ctor_get(v___x_828_, 0);
v_nextMacroScope_832_ = lean_ctor_get(v___x_828_, 1);
v_ngen_833_ = lean_ctor_get(v___x_828_, 2);
v_auxDeclNGen_834_ = lean_ctor_get(v___x_828_, 3);
v_traceState_835_ = lean_ctor_get(v___x_828_, 4);
v_cache_836_ = lean_ctor_get(v___x_828_, 5);
v_messages_837_ = lean_ctor_get(v___x_828_, 6);
v_infoState_838_ = lean_ctor_get(v___x_828_, 7);
v_snapshotTasks_839_ = lean_ctor_get(v___x_828_, 8);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_853_ == 0)
{
v___x_841_ = v___x_828_;
v_isShared_842_ = v_isSharedCheck_853_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snapshotTasks_839_);
lean_inc(v_infoState_838_);
lean_inc(v_messages_837_);
lean_inc(v_cache_836_);
lean_inc(v_traceState_835_);
lean_inc(v_auxDeclNGen_834_);
lean_inc(v_ngen_833_);
lean_inc(v_nextMacroScope_832_);
lean_inc(v_env_831_);
lean_dec(v___x_828_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_853_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
lean_inc(v_openDecls_830_);
lean_inc(v_currNamespace_829_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_currNamespace_829_);
lean_ctor_set(v___x_843_, 1, v_openDecls_830_);
v___x_844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v___y_821_);
lean_inc_ref(v___y_824_);
lean_inc_ref(v___y_822_);
v___x_845_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_845_, 0, v___y_822_);
lean_ctor_set(v___x_845_, 1, v___y_823_);
lean_ctor_set(v___x_845_, 2, v___y_820_);
lean_ctor_set(v___x_845_, 3, v___y_824_);
lean_ctor_set(v___x_845_, 4, v___x_844_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*5, v___y_819_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*5 + 1, v___y_825_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*5 + 2, v_isSilent_812_);
v___x_846_ = l_Lean_MessageLog_add(v___x_845_, v_messages_837_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 6, v___x_846_);
v___x_848_ = v___x_841_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_env_831_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_nextMacroScope_832_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_ngen_833_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_auxDeclNGen_834_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v_traceState_835_);
lean_ctor_set(v_reuseFailAlloc_852_, 5, v_cache_836_);
lean_ctor_set(v_reuseFailAlloc_852_, 6, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 7, v_infoState_838_);
lean_ctor_set(v_reuseFailAlloc_852_, 8, v_snapshotTasks_839_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_st_ref_set(v___y_827_, v___x_848_);
v___x_850_ = lean_box(0);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
}
v___jp_854_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_878_; 
v___x_863_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_810_);
v___x_864_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6_spec__8(v___x_863_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_878_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_inc_ref_n(v___y_859_, 2);
v___x_869_ = l_Lean_FileMap_toPosition(v___y_859_, v___y_861_);
lean_dec(v___y_861_);
v___x_870_ = l_Lean_FileMap_toPosition(v___y_859_, v___y_862_);
lean_dec(v___y_862_);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
if (v___y_858_ == 0)
{
lean_del_object(v___x_867_);
lean_dec_ref(v___y_855_);
v___y_819_ = v___y_856_;
v___y_820_ = v___x_871_;
v___y_821_ = v_a_865_;
v___y_822_ = v___y_857_;
v___y_823_ = v___x_869_;
v___y_824_ = v___x_872_;
v___y_825_ = v___y_860_;
v___y_826_ = v___y_815_;
v___y_827_ = v___y_816_;
goto v___jp_818_;
}
else
{
uint8_t v___x_873_; 
lean_inc(v_a_865_);
v___x_873_ = l_Lean_MessageData_hasTag(v___y_855_, v_a_865_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec_ref_known(v___x_871_, 1);
lean_dec_ref(v___x_869_);
lean_dec(v_a_865_);
v___x_874_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_874_);
v___x_876_ = v___x_867_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_del_object(v___x_867_);
v___y_819_ = v___y_856_;
v___y_820_ = v___x_871_;
v___y_821_ = v_a_865_;
v___y_822_ = v___y_857_;
v___y_823_ = v___x_869_;
v___y_824_ = v___x_872_;
v___y_825_ = v___y_860_;
v___y_826_ = v___y_815_;
v___y_827_ = v___y_816_;
goto v___jp_818_;
}
}
}
}
v___jp_879_:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Syntax_getTailPos_x3f(v___y_882_, v___y_881_);
lean_dec(v___y_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_inc(v___y_887_);
v___y_855_ = v___y_880_;
v___y_856_ = v___y_881_;
v___y_857_ = v___y_883_;
v___y_858_ = v___y_884_;
v___y_859_ = v___y_885_;
v___y_860_ = v___y_886_;
v___y_861_ = v___y_887_;
v___y_862_ = v___y_887_;
goto v___jp_854_;
}
else
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_888_, 1);
v___y_855_ = v___y_880_;
v___y_856_ = v___y_881_;
v___y_857_ = v___y_883_;
v___y_858_ = v___y_884_;
v___y_859_ = v___y_885_;
v___y_860_ = v___y_886_;
v___y_861_ = v___y_887_;
v___y_862_ = v_val_889_;
goto v___jp_854_;
}
}
v___jp_890_:
{
lean_object* v_ref_898_; lean_object* v___x_899_; 
v_ref_898_ = l_Lean_replaceRef(v_ref_809_, v___y_893_);
v___x_899_ = l_Lean_Syntax_getPos_x3f(v_ref_898_, v___y_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___y_880_ = v___y_891_;
v___y_881_ = v___y_892_;
v___y_882_ = v_ref_898_;
v___y_883_ = v___y_894_;
v___y_884_ = v___y_895_;
v___y_885_ = v___y_896_;
v___y_886_ = v___y_897_;
v___y_887_ = v___x_900_;
goto v___jp_879_;
}
else
{
lean_object* v_val_901_; 
v_val_901_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v___x_899_, 1);
v___y_880_ = v___y_891_;
v___y_881_ = v___y_892_;
v___y_882_ = v_ref_898_;
v___y_883_ = v___y_894_;
v___y_884_ = v___y_895_;
v___y_885_ = v___y_896_;
v___y_886_ = v___y_897_;
v___y_887_ = v_val_901_;
goto v___jp_879_;
}
}
v___jp_903_:
{
if (v___y_910_ == 0)
{
v___y_891_ = v___y_904_;
v___y_892_ = v___y_909_;
v___y_893_ = v___y_905_;
v___y_894_ = v___y_906_;
v___y_895_ = v___y_907_;
v___y_896_ = v___y_908_;
v___y_897_ = v_severity_811_;
goto v___jp_890_;
}
else
{
v___y_891_ = v___y_904_;
v___y_892_ = v___y_909_;
v___y_893_ = v___y_905_;
v___y_894_ = v___y_906_;
v___y_895_ = v___y_907_;
v___y_896_ = v___y_908_;
v___y_897_ = v___x_902_;
goto v___jp_890_;
}
}
v___jp_911_:
{
if (v___y_912_ == 0)
{
lean_object* v_fileName_913_; lean_object* v_fileMap_914_; lean_object* v_options_915_; lean_object* v_ref_916_; uint8_t v_suppressElabErrors_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___f_920_; uint8_t v___x_921_; uint8_t v___x_922_; 
v_fileName_913_ = lean_ctor_get(v___y_815_, 0);
v_fileMap_914_ = lean_ctor_get(v___y_815_, 1);
v_options_915_ = lean_ctor_get(v___y_815_, 2);
v_ref_916_ = lean_ctor_get(v___y_815_, 5);
v_suppressElabErrors_917_ = lean_ctor_get_uint8(v___y_815_, sizeof(void*)*14 + 1);
v___x_918_ = lean_box(v___y_912_);
v___x_919_ = lean_box(v_suppressElabErrors_917_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_920_, 0, v___x_918_);
lean_closure_set(v___f_920_, 1, v___x_919_);
v___x_921_ = 1;
v___x_922_ = l_Lean_instBEqMessageSeverity_beq(v_severity_811_, v___x_921_);
if (v___x_922_ == 0)
{
v___y_904_ = v___f_920_;
v___y_905_ = v_ref_916_;
v___y_906_ = v_fileName_913_;
v___y_907_ = v_suppressElabErrors_917_;
v___y_908_ = v_fileMap_914_;
v___y_909_ = v___y_912_;
v___y_910_ = v___x_922_;
goto v___jp_903_;
}
else
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = l_Lean_warningAsError;
v___x_924_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_options_915_, v___x_923_);
v___y_904_ = v___f_920_;
v___y_905_ = v_ref_916_;
v___y_906_ = v_fileName_913_;
v___y_907_ = v_suppressElabErrors_917_;
v___y_908_ = v_fileMap_914_;
v___y_909_ = v___y_912_;
v___y_910_ = v___x_924_;
goto v___jp_903_;
}
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_msgData_810_);
v___x_925_ = lean_box(0);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_ref_929_, lean_object* v_msgData_930_, lean_object* v_severity_931_, lean_object* v_isSilent_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v_severity_boxed_938_; uint8_t v_isSilent_boxed_939_; lean_object* v_res_940_; 
v_severity_boxed_938_ = lean_unbox(v_severity_931_);
v_isSilent_boxed_939_ = lean_unbox(v_isSilent_932_);
v_res_940_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_929_, v_msgData_930_, v_severity_boxed_938_, v_isSilent_boxed_939_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v_ref_929_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_msgData_941_, uint8_t v_severity_942_, uint8_t v_isSilent_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_ref_949_; lean_object* v___x_950_; 
v_ref_949_ = lean_ctor_get(v___y_946_, 5);
v___x_950_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_949_, v_msgData_941_, v_severity_942_, v_isSilent_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_msgData_951_, lean_object* v_severity_952_, lean_object* v_isSilent_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v_severity_boxed_959_; uint8_t v_isSilent_boxed_960_; lean_object* v_res_961_; 
v_severity_boxed_959_ = lean_unbox(v_severity_952_);
v_isSilent_boxed_960_ = lean_unbox(v_isSilent_953_);
v_res_961_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(v_msgData_951_, v_severity_boxed_959_, v_isSilent_boxed_960_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(lean_object* v_msgData_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v___x_968_ = 1;
v___x_969_ = 0;
v___x_970_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4(v_msgData_962_, v___x_968_, v___x_969_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3___boxed(lean_object* v_msgData_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(v_msgData_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_978_, uint64_t v_k_979_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_992_, lean_object* v_k_993_){
_start:
{
uint64_t v_k_boxed_994_; lean_object* v_res_995_; 
v_k_boxed_994_ = lean_unbox_uint64(v_k_993_);
lean_dec_ref(v_k_993_);
v_res_995_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_t_992_, v_k_boxed_994_);
lean_dec(v_t_992_);
return v_res_995_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__7_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v_stx_1008_, uint8_t v_builtin_1009_, lean_object* v_decl_1010_, lean_object* v___x_1011_, lean_object* v___x_1012_, uint8_t v___x_1013_, uint8_t v_kind_1014_, lean_object* v_name_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1008_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1122_) == 0)
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
lean_dec_ref_known(v___x_1122_, 1);
v___x_1123_ = 0;
v___x_1124_ = l_Lean_instBEqAttributeKind_beq(v_kind_1014_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
v___x_1125_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_1015_, v_kind_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
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
lean_dec(v_name_1015_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
return v___x_1122_;
}
v___jp_1021_:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_st_ref_get(v___y_1028_);
if (v_builtin_1009_ == 0)
{
lean_object* v_env_1030_; uint64_t v_javascriptHash_1031_; lean_object* v___x_1032_; lean_object* v_toEnvExtension_1033_; lean_object* v_asyncMode_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v___y_1022_);
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_env_1030_);
lean_dec(v___x_1029_);
v_javascriptHash_1031_ = lean_ctor_get_uint64(v___y_1024_, sizeof(void*)*1);
lean_dec_ref(v___y_1024_);
v___x_1032_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1033_ = lean_ctor_get(v___x_1032_, 0);
v_asyncMode_1034_ = lean_ctor_get(v_toEnvExtension_1033_, 2);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_decl_1010_);
lean_ctor_set(v___x_1035_, 1, v___y_1023_);
v___x_1036_ = lean_box_uint64(v_javascriptHash_1031_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1032_, v_env_1030_, v___x_1037_, v_asyncMode_1034_, v___x_1038_);
v___x_1040_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg(v___x_1039_, v___y_1026_, v___y_1028_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v___x_1029_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc_n(v_decl_1010_, 2);
v___x_1041_ = l_Lean_mkConst(v_decl_1010_, v___y_1022_);
v___x_1042_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1043_ = l_Lean_Name_mkStr3(v___x_1011_, v___x_1012_, v___x_1042_);
v___x_1044_ = l_Lean_mkConst(v___x_1043_, v___y_1022_);
v___x_1045_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_1010_);
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
v_asyncMode_1059_ = lean_ctor_get(v_toEnvExtension_1058_, 2);
v_javascriptHash_1060_ = lean_ctor_get_uint64(v___y_1051_, sizeof(void*)*1);
v___x_1061_ = lean_box(1);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1061_, v___x_1057_, v___y_1052_, v_asyncMode_1059_, v___x_1062_);
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1063_, v_javascriptHash_1060_);
lean_dec(v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 1)
{
lean_object* v_val_1065_; lean_object* v_fst_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1078_; 
v_val_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v___x_1064_, 1);
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
v___x_1070_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
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
v___x_1074_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(v___x_1075_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_dec_ref_known(v___x_1076_, 1);
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
lean_dec_ref(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
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
v___x_1085_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1086_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
lean_inc_ref(v___x_1012_);
lean_inc_ref(v___x_1011_);
v___x_1087_ = l_Lean_Name_mkStr4(v___x_1011_, v___x_1012_, v___x_1085_, v___x_1086_);
v___x_1088_ = lean_box(0);
lean_inc(v_decl_1010_);
v___x_1089_ = l_Lean_Expr_const___override(v_decl_1010_, v___x_1088_);
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_mk_empty_array_with_capacity(v___x_1090_);
v___x_1092_ = lean_array_push(v___x_1091_, v___x_1089_);
v___x_1093_ = l_Lean_Meta_mkAppM(v___x_1087_, v___x_1092_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_n(v_a_1094_, 2);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_1094_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
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
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1100_, v_javascriptHash_1101_);
lean_dec(v___x_1100_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref_known(v___x_1102_, 1);
v___x_1103_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__8_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1104_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3(v___x_1103_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref_known(v___x_1104_, 1);
v___y_1049_ = v___x_1088_;
v___y_1050_ = v_a_1094_;
v___y_1051_ = v_a_1096_;
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
lean_dec_ref(v___x_1012_);
lean_dec_ref(v___x_1011_);
lean_dec(v_decl_1010_);
return v___x_1104_;
}
}
else
{
lean_dec(v___x_1102_);
v___y_1049_ = v___x_1088_;
v___y_1050_ = v_a_1094_;
v___y_1051_ = v_a_1096_;
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
v___y_1049_ = v___x_1088_;
v___y_1050_ = v_a_1094_;
v___y_1051_ = v_a_1096_;
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_stx_1126_, lean_object* v_builtin_1127_, lean_object* v_decl_1128_, lean_object* v___x_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v_kind_1132_, lean_object* v_name_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v_builtin_boxed_1139_; uint8_t v___x_11295__boxed_1140_; uint8_t v_kind_boxed_1141_; lean_object* v_res_1142_; 
v_builtin_boxed_1139_ = lean_unbox(v_builtin_1127_);
v___x_11295__boxed_1140_ = lean_unbox(v___x_1131_);
v_kind_boxed_1141_ = lean_unbox(v_kind_1132_);
v_res_1142_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v_stx_1126_, v_builtin_boxed_1139_, v_decl_1128_, v___x_1129_, v___x_1130_, v___x_11295__boxed_1140_, v_kind_boxed_1141_, v_name_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object* v___y_1143_, uint8_t v_isExporting_1144_, lean_object* v___x_1145_, lean_object* v___y_1146_, lean_object* v___x_1147_, lean_object* v_a_x3f_1148_){
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object* v___y_1185_, lean_object* v_isExporting_1186_, lean_object* v___x_1187_, lean_object* v___y_1188_, lean_object* v___x_1189_, lean_object* v_a_x3f_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_isExporting_boxed_1192_; lean_object* v_res_1193_; 
v_isExporting_boxed_1192_ = lean_unbox(v_isExporting_1186_);
v_res_1193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1185_, v_isExporting_boxed_1192_, v___x_1187_, v___y_1188_, v___x_1189_, v_a_x3f_1190_);
lean_dec(v_a_x3f_1190_);
lean_dec(v___y_1188_);
lean_dec(v___y_1185_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object* v_x_1194_, uint8_t v_isExporting_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_env_1202_; uint8_t v_isExporting_1203_; uint8_t v___y_1270_; lean_object* v___x_1272_; uint8_t v_isModule_1273_; uint8_t v___x_1274_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v_isExporting_1203_ = lean_ctor_get_uint8(v_env_1202_, sizeof(void*)*8);
v___x_1272_ = l_Lean_Environment_header(v_env_1202_);
lean_dec_ref(v_env_1202_);
v_isModule_1273_ = lean_ctor_get_uint8(v___x_1272_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1272_);
v___x_1274_ = lean_bool_not(v_isModule_1273_);
if (v___x_1274_ == 0)
{
if (v_isExporting_1203_ == 0)
{
if (v_isExporting_1195_ == 0)
{
lean_object* v___x_1275_; 
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v___x_1275_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1275_;
}
else
{
goto v___jp_1204_;
}
}
else
{
v___y_1270_ = v_isExporting_1195_;
goto v___jp_1269_;
}
}
else
{
v___y_1270_ = v___x_1274_;
goto v___jp_1269_;
}
v___jp_1204_:
{
lean_object* v___x_1205_; lean_object* v_env_1206_; lean_object* v_nextMacroScope_1207_; lean_object* v_ngen_1208_; lean_object* v_auxDeclNGen_1209_; lean_object* v_traceState_1210_; lean_object* v_messages_1211_; lean_object* v_infoState_1212_; lean_object* v_snapshotTasks_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1267_; 
v___x_1205_ = lean_st_ref_take(v___y_1199_);
v_env_1206_ = lean_ctor_get(v___x_1205_, 0);
v_nextMacroScope_1207_ = lean_ctor_get(v___x_1205_, 1);
v_ngen_1208_ = lean_ctor_get(v___x_1205_, 2);
v_auxDeclNGen_1209_ = lean_ctor_get(v___x_1205_, 3);
v_traceState_1210_ = lean_ctor_get(v___x_1205_, 4);
v_messages_1211_ = lean_ctor_get(v___x_1205_, 6);
v_infoState_1212_ = lean_ctor_get(v___x_1205_, 7);
v_snapshotTasks_1213_ = lean_ctor_get(v___x_1205_, 8);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1205_, 5);
lean_dec(v_unused_1268_);
v___x_1215_ = v___x_1205_;
v_isShared_1216_ = v_isSharedCheck_1267_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_snapshotTasks_1213_);
lean_inc(v_infoState_1212_);
lean_inc(v_messages_1211_);
lean_inc(v_traceState_1210_);
lean_inc(v_auxDeclNGen_1209_);
lean_inc(v_ngen_1208_);
lean_inc(v_nextMacroScope_1207_);
lean_inc(v_env_1206_);
lean_dec(v___x_1205_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1267_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = l_Lean_Environment_setExporting(v_env_1206_, v_isExporting_1195_);
v___x_1218_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 5, v___x_1218_);
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_nextMacroScope_1207_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_ngen_1208_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v_auxDeclNGen_1209_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_traceState_1210_);
lean_ctor_set(v_reuseFailAlloc_1266_, 5, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1266_, 6, v_messages_1211_);
lean_ctor_set(v_reuseFailAlloc_1266_, 7, v_infoState_1212_);
lean_ctor_set(v_reuseFailAlloc_1266_, 8, v_snapshotTasks_1213_);
v___x_1220_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_mctx_1223_; lean_object* v_zetaDeltaFVarIds_1224_; lean_object* v_postponed_1225_; lean_object* v_diag_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1264_; 
v___x_1221_ = lean_st_ref_set(v___y_1199_, v___x_1220_);
v___x_1222_ = lean_st_ref_take(v___y_1197_);
v_mctx_1223_ = lean_ctor_get(v___x_1222_, 0);
v_zetaDeltaFVarIds_1224_ = lean_ctor_get(v___x_1222_, 2);
v_postponed_1225_ = lean_ctor_get(v___x_1222_, 3);
v_diag_1226_ = lean_ctor_get(v___x_1222_, 4);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1222_, 1);
lean_dec(v_unused_1265_);
v___x_1228_ = v___x_1222_;
v_isShared_1229_ = v_isSharedCheck_1264_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_diag_1226_);
lean_inc(v_postponed_1225_);
lean_inc(v_zetaDeltaFVarIds_1224_);
lean_inc(v_mctx_1223_);
lean_dec(v___x_1222_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1264_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1230_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_mctx_1223_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_zetaDeltaFVarIds_1224_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_postponed_1225_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_diag_1226_);
v___x_1232_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v_r_1234_; 
v___x_1233_ = lean_st_ref_set(v___y_1197_, v___x_1232_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v_r_1234_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
if (lean_obj_tag(v_r_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1251_; 
v_a_1235_ = lean_ctor_get(v_r_1234_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_r_1234_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1237_ = v_r_1234_;
v_isShared_1238_ = v_isSharedCheck_1251_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v_r_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1251_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
lean_inc(v_a_1235_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 1);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v___x_1241_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1199_, v_isExporting_1203_, v___x_1218_, v___y_1197_, v___x_1230_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1249_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_a_1235_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1235_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_a_1252_ = lean_ctor_get(v_r_1234_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v_r_1234_, 1);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1199_, v_isExporting_1203_, v___x_1218_, v___y_1197_, v___x_1230_, v___x_1253_);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1254_, 0);
lean_dec(v_unused_1262_);
v___x_1256_ = v___x_1254_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v___x_1254_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 1);
lean_ctor_set(v___x_1256_, 0, v_a_1252_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1252_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
}
}
v___jp_1269_:
{
if (v___y_1270_ == 0)
{
goto v___jp_1204_;
}
else
{
lean_object* v___x_1271_; 
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v___x_1271_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object* v_x_1276_, lean_object* v_isExporting_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v_isExporting_boxed_1283_; lean_object* v_res_1284_; 
v_isExporting_boxed_1283_ = lean_unbox(v_isExporting_1277_);
v_res_1284_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1276_, v_isExporting_boxed_1283_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(lean_object* v_x_1285_, uint8_t v_when_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
if (v_when_1286_ == 0)
{
lean_object* v___x_1292_; 
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
v___x_1292_ = lean_apply_5(v_x_1285_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, lean_box(0));
return v___x_1292_;
}
else
{
uint8_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = 0;
v___x_1294_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1285_, v___x_1293_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_x_1295_, lean_object* v_when_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_when_boxed_1302_; lean_object* v_res_1303_; 
v_when_boxed_1302_ = lean_unbox(v_when_1296_);
v_res_1303_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v_x_1295_, v_when_boxed_1302_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1303_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1304_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_box(1);
v___x_1308_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1309_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
lean_ctor_set(v___x_1310_, 2, v___x_1307_);
return v___x_1310_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set(v___x_1315_, 2, v___x_1314_);
lean_ctor_set(v___x_1315_, 3, v___x_1314_);
lean_ctor_set(v___x_1315_, 4, v___x_1313_);
lean_ctor_set(v___x_1315_, 5, v___x_1313_);
lean_ctor_set(v___x_1315_, 6, v___x_1313_);
lean_ctor_set(v___x_1315_, 7, v___x_1313_);
lean_ctor_set(v___x_1315_, 8, v___x_1313_);
lean_ctor_set(v___x_1315_, 9, v___x_1313_);
return v___x_1315_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1317_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
lean_ctor_set(v___x_1317_, 2, v___x_1316_);
lean_ctor_set(v___x_1317_, 3, v___x_1316_);
lean_ctor_set(v___x_1317_, 4, v___x_1316_);
lean_ctor_set(v___x_1317_, 5, v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_ctor_set(v___x_1319_, 2, v___x_1318_);
lean_ctor_set(v___x_1319_, 3, v___x_1318_);
lean_ctor_set(v___x_1319_, 4, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(uint8_t v___x_1320_, lean_object* v___x_1321_, uint8_t v_builtin_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_name_1325_, lean_object* v_decl_1326_, lean_object* v_stx_1327_, uint8_t v_kind_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v___x_1332_; uint8_t v___x_1333_; uint8_t v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; uint64_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; 
v___x_1332_ = 0;
v___x_1333_ = 1;
v___x_1334_ = 0;
v___x_1335_ = 2;
v___x_1336_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1336_, 0, v___x_1332_);
lean_ctor_set_uint8(v___x_1336_, 1, v___x_1332_);
lean_ctor_set_uint8(v___x_1336_, 2, v___x_1332_);
lean_ctor_set_uint8(v___x_1336_, 3, v___x_1332_);
lean_ctor_set_uint8(v___x_1336_, 4, v___x_1332_);
lean_ctor_set_uint8(v___x_1336_, 5, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 6, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 7, v___x_1332_);
lean_ctor_set_uint8(v___x_1336_, 8, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 9, v___x_1333_);
lean_ctor_set_uint8(v___x_1336_, 10, v___x_1334_);
lean_ctor_set_uint8(v___x_1336_, 11, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 12, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 13, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 14, v___x_1335_);
lean_ctor_set_uint8(v___x_1336_, 15, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 16, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 17, v___x_1320_);
lean_ctor_set_uint8(v___x_1336_, 18, v___x_1320_);
v___x_1337_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set_uint64(v___x_1338_, sizeof(void*)*1, v___x_1337_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1341_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1342_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1343_ = lean_box(0);
lean_inc(v___x_1321_);
v___x_1344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1344_, 0, v___x_1338_);
lean_ctor_set(v___x_1344_, 1, v___x_1321_);
lean_ctor_set(v___x_1344_, 2, v___x_1341_);
lean_ctor_set(v___x_1344_, 3, v___x_1342_);
lean_ctor_set(v___x_1344_, 4, v___x_1343_);
lean_ctor_set(v___x_1344_, 5, v___x_1339_);
lean_ctor_set(v___x_1344_, 6, v___x_1343_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7, v___x_1332_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7 + 1, v___x_1332_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7 + 2, v___x_1332_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7 + 3, v___x_1320_);
v___x_1345_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1346_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1347_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1345_);
lean_ctor_set(v___x_1348_, 1, v___x_1346_);
lean_ctor_set(v___x_1348_, 2, v___x_1321_);
lean_ctor_set(v___x_1348_, 3, v___x_1340_);
lean_ctor_set(v___x_1348_, 4, v___x_1347_);
v___x_1349_ = lean_st_mk_ref(v___x_1348_);
v___x_1350_ = lean_box(v_builtin_1322_);
v___x_1351_ = lean_box(v___x_1320_);
v___x_1352_ = lean_box(v_kind_1328_);
v___f_1353_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 13, 8);
lean_closure_set(v___f_1353_, 0, v_stx_1327_);
lean_closure_set(v___f_1353_, 1, v___x_1350_);
lean_closure_set(v___f_1353_, 2, v_decl_1326_);
lean_closure_set(v___f_1353_, 3, v___x_1323_);
lean_closure_set(v___f_1353_, 4, v___x_1324_);
lean_closure_set(v___f_1353_, 5, v___x_1351_);
lean_closure_set(v___f_1353_, 6, v___x_1352_);
lean_closure_set(v___f_1353_, 7, v_name_1325_);
v___x_1354_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v___f_1353_, v___x_1320_, v___x_1344_, v___x_1349_, v___y_1329_, v___y_1330_);
lean_dec_ref_known(v___x_1344_, 7);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1363_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = lean_st_ref_get(v___x_1349_);
lean_dec(v___x_1349_);
lean_dec(v___x_1359_);
if (v_isShared_1358_ == 0)
{
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1355_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_dec(v___x_1349_);
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v___x_1364_, lean_object* v___x_1365_, lean_object* v_builtin_1366_, lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v_name_1369_, lean_object* v_decl_1370_, lean_object* v_stx_1371_, lean_object* v_kind_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_11839__boxed_1376_; uint8_t v_builtin_boxed_1377_; uint8_t v_kind_boxed_1378_; lean_object* v_res_1379_; 
v___x_11839__boxed_1376_ = lean_unbox(v___x_1364_);
v_builtin_boxed_1377_ = lean_unbox(v_builtin_1366_);
v_kind_boxed_1378_ = lean_unbox(v_kind_1372_);
v_res_1379_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_11839__boxed_1376_, v___x_1365_, v_builtin_boxed_1377_, v___x_1367_, v___x_1368_, v_name_1369_, v_decl_1370_, v_stx_1371_, v_kind_boxed_1378_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v___x_1387_, uint8_t v_builtin_1388_, lean_object* v_name_1389_){
_start:
{
lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___y_1400_; 
lean_inc_n(v_name_1389_, 2);
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1391_, 0, v_name_1389_);
v___x_1392_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0));
v___x_1393_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1));
v___x_1394_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1395_ = 1;
v___x_1396_ = lean_box(v___x_1395_);
v___x_1397_ = lean_box(v_builtin_1388_);
v___f_1398_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1398_, 0, v___x_1396_);
lean_closure_set(v___f_1398_, 1, v___x_1387_);
lean_closure_set(v___f_1398_, 2, v___x_1397_);
lean_closure_set(v___f_1398_, 3, v___x_1392_);
lean_closure_set(v___f_1398_, 4, v___x_1393_);
lean_closure_set(v___f_1398_, 5, v_name_1389_);
if (v_builtin_1388_ == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___y_1400_ = v___x_1423_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___y_1400_ = v___x_1424_;
goto v___jp_1399_;
}
v___jp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v_impl_1405_; lean_object* v___x_1406_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
lean_inc_ref(v___y_1400_);
v___x_1402_ = lean_string_append(v___y_1400_, v___x_1401_);
v___x_1403_ = 1;
v___x_1404_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1404_, 0, v___x_1394_);
lean_ctor_set(v___x_1404_, 1, v_name_1389_);
lean_ctor_set(v___x_1404_, 2, v___x_1402_);
lean_ctor_set_uint8(v___x_1404_, sizeof(void*)*3, v___x_1403_);
v_impl_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_impl_1405_, 0, v___x_1404_);
lean_ctor_set(v_impl_1405_, 1, v___f_1398_);
lean_ctor_set(v_impl_1405_, 2, v___f_1391_);
lean_inc_ref(v_impl_1405_);
v___x_1406_ = l_Lean_registerBuiltinAttribute(v_impl_1405_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1406_, 0);
lean_dec(v_unused_1414_);
v___x_1408_ = v___x_1406_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v___x_1406_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v_impl_1405_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_impl_1405_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref_known(v_impl_1405_, 3);
v_a_1415_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1406_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1406_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v___x_1425_, lean_object* v_builtin_1426_, lean_object* v_name_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v_builtin_boxed_1429_; lean_object* v_res_1430_; 
v_builtin_boxed_1429_ = lean_unbox(v_builtin_1426_);
v_res_1430_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1425_, v_builtin_boxed_1429_, v_name_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = lean_box(1);
v___x_1439_ = 1;
v___x_1440_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1441_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1438_, v___x_1439_, v___x_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_dec_ref_known(v___x_1441_, 1);
v___x_1442_ = 0;
v___x_1443_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1444_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1438_, v___x_1442_, v___x_1443_);
return v___x_1444_;
}
else
{
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1447_, lean_object* v_msg_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v_msg_1448_, v___y_1449_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1453_, lean_object* v_msg_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(v_00_u03b1_1453_, v_msg_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_1459_, lean_object* v_t_1460_, uint64_t v_k_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_t_1460_, v_k_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_1463_, lean_object* v_t_1464_, lean_object* v_k_1465_){
_start:
{
uint64_t v_k_boxed_1466_; lean_object* v_res_1467_; 
v_k_boxed_1466_ = lean_unbox_uint64(v_k_1465_);
lean_dec_ref(v_k_1465_);
v_res_1467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(v_00_u03b4_1463_, v_t_1464_, v_k_boxed_1466_);
lean_dec(v_t_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1468_, lean_object* v_name_1469_, uint8_t v_kind_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_1469_, v_kind_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_name_1478_, lean_object* v_kind_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v_kind_boxed_1485_; lean_object* v_res_1486_; 
v_kind_boxed_1485_ = lean_unbox(v_kind_1479_);
v_res_1486_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(v_00_u03b1_1477_, v_name_1478_, v_kind_boxed_1485_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(lean_object* v_00_u03b1_1487_, lean_object* v_x_1488_, uint8_t v_isExporting_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1488_, v_isExporting_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_x_1497_, lean_object* v_isExporting_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_isExporting_boxed_1504_; lean_object* v_res_1505_; 
v_isExporting_boxed_1504_ = lean_unbox(v_isExporting_1498_);
v_res_1505_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(v_00_u03b1_1496_, v_x_1497_, v_isExporting_boxed_1504_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1506_, lean_object* v_x_1507_, uint8_t v_when_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v_x_1507_, v_when_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_x_1516_, lean_object* v_when_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_when_boxed_1523_; lean_object* v_res_1524_; 
v_when_boxed_1523_ = lean_unbox(v_when_1517_);
v_res_1524_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(v_00_u03b1_1515_, v_x_1516_, v_when_boxed_1523_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1533_, lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1533_, v_msg_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
if (lean_obj_tag(v_a_1541_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_array_to_list(v_a_1542_);
return v___x_1543_;
}
else
{
lean_object* v_head_1544_; lean_object* v_tail_1545_; lean_object* v___x_1546_; 
v_head_1544_ = lean_ctor_get(v_a_1541_, 0);
lean_inc(v_head_1544_);
v_tail_1545_ = lean_ctor_get(v_a_1541_, 1);
lean_inc(v_tail_1545_);
lean_dec_ref_known(v_a_1541_, 2);
v___x_1546_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1542_, v_head_1544_);
v_a_1541_ = v_tail_1545_;
v_a_1542_ = v___x_1546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object* v_x_1552_){
_start:
{
uint64_t v_hash_1553_; lean_object* v_pos_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_hash_1553_ = lean_ctor_get_uint64(v_x_1552_, sizeof(void*)*1);
v_pos_1554_ = lean_ctor_get(v_x_1552_, 0);
lean_inc_ref(v_pos_1554_);
lean_dec_ref(v_x_1552_);
v___x_1555_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
v___x_1556_ = lean_uint64_to_nat(v_hash_1553_);
v___x_1557_ = l_Lean_bignumToJson(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1555_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1562_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_1554_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1559_);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1559_);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1560_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1568_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1566_, v___x_1567_);
v___x_1569_ = l_Lean_Json_mkObj(v___x_1568_);
lean_dec(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object* v_j_1572_, lean_object* v_k_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = l_Lean_Json_getObjValD(v_j_1572_, v_k_1573_);
v___x_1575_ = l_Lean_UInt64_fromJson_x3f(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object* v_j_1576_, lean_object* v_k_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_j_1576_, v_k_1577_);
lean_dec_ref(v_k_1577_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object* v_j_1579_, lean_object* v_k_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = l_Lean_Json_getObjValD(v_j_1579_, v_k_1580_);
v___x_1582_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object* v_j_1583_, lean_object* v_k_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_j_1583_, v_k_1584_);
lean_dec_ref(v_k_1584_);
return v_res_1585_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = 1;
v___x_1592_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1));
v___x_1593_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1592_, v___x_1591_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1595_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2);
v___x_1596_ = lean_string_append(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = 1;
v___x_1600_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4));
v___x_1601_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1600_, v___x_1599_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5);
v___x_1603_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1604_ = lean_string_append(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1607_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6);
v___x_1608_ = lean_string_append(v___x_1607_, v___x_1606_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = 1;
v___x_1612_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9));
v___x_1613_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1612_, v___x_1611_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10);
v___x_1615_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1616_ = lean_string_append(v___x_1615_, v___x_1614_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1618_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11);
v___x_1619_ = lean_string_append(v___x_1618_, v___x_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object* v_json_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
lean_inc(v_json_1620_);
v___x_1622_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_json_1620_, v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_json_1620_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1627_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8);
v___x_1628_ = lean_string_append(v___x_1627_, v_a_1623_);
lean_dec(v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1628_);
v___x_1630_ = v___x_1625_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
else
{
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_json_1620_);
v_a_1633_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1622_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1622_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 0);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
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
lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1641_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1642_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1643_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_json_1620_, v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1641_);
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1653_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1653_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1648_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12);
v___x_1649_ = lean_string_append(v___x_1648_, v_a_1644_);
lean_dec(v_a_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1649_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_a_1641_);
v_a_1654_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1643_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1643_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 0);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1671_; 
v_a_1662_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1664_ = v___x_1643_;
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1643_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; uint64_t v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1666_, 0, v_a_1662_);
v___x_1667_ = lean_unbox_uint64(v_a_1641_);
lean_dec(v_a_1641_);
lean_ctor_set_uint64(v___x_1666_, sizeof(void*)*1, v___x_1667_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1666_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1666_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson(lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1678_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_x_1677_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
v___x_1684_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1685_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1683_, v___x_1684_);
v___x_1686_ = l_Lean_Json_mkObj(v___x_1685_);
lean_dec(v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(lean_object* v_j_1689_, lean_object* v_k_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = l_Lean_Json_getObjValD(v_j_1689_, v_k_1690_);
v___x_1692_ = l_Lean_Json_getStr_x3f(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0___boxed(lean_object* v_j_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_j_1693_, v_k_1694_);
lean_dec_ref(v_k_1694_);
return v_res_1695_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = 1;
v___x_1702_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1));
v___x_1703_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1702_, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1705_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2);
v___x_1706_ = lean_string_append(v___x_1705_, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = 1;
v___x_1710_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4));
v___x_1711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1710_, v___x_1709_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5);
v___x_1713_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3);
v___x_1714_ = lean_string_append(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1716_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6);
v___x_1717_ = lean_string_append(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson(lean_object* v_json_1718_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1720_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_1718_, v___x_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1730_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1725_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7);
v___x_1726_ = lean_string_append(v___x_1725_, v_a_1721_);
lean_dec(v_a_1721_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1720_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1720_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 0);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1720_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1720_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object* v___y_1749_){
_start:
{
lean_object* v_doc_1751_; lean_object* v___x_1752_; 
v_doc_1751_ = lean_ctor_get(v___y_1749_, 1);
lean_inc_ref(v_doc_1751_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_doc_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1753_);
lean_dec_ref(v___y_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t v_k_1756_, lean_object* v_t_1757_){
_start:
{
if (lean_obj_tag(v_t_1757_) == 0)
{
lean_object* v_k_1758_; lean_object* v_l_1759_; lean_object* v_r_1760_; uint64_t v___x_1761_; uint8_t v___x_1762_; 
v_k_1758_ = lean_ctor_get(v_t_1757_, 1);
v_l_1759_ = lean_ctor_get(v_t_1757_, 3);
v_r_1760_ = lean_ctor_get(v_t_1757_, 4);
v___x_1761_ = lean_unbox_uint64(v_k_1758_);
v___x_1762_ = lean_uint64_dec_lt(v_k_1756_, v___x_1761_);
if (v___x_1762_ == 0)
{
uint64_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_unbox_uint64(v_k_1758_);
v___x_1764_ = lean_uint64_dec_eq(v_k_1756_, v___x_1763_);
if (v___x_1764_ == 0)
{
v_t_1757_ = v_r_1760_;
goto _start;
}
else
{
return v___x_1764_;
}
}
else
{
v_t_1757_ = v_l_1759_;
goto _start;
}
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object* v_k_1768_, lean_object* v_t_1769_){
_start:
{
uint64_t v_k_boxed_1770_; uint8_t v_res_1771_; lean_object* v_r_1772_; 
v_k_boxed_1770_ = lean_unbox_uint64(v_k_1768_);
lean_dec_ref(v_k_1768_);
v_res_1771_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_boxed_1770_, v_t_1769_);
lean_dec(v_t_1769_);
v_r_1772_ = lean_box(v_res_1771_);
return v_r_1772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object* v___x_1773_, uint64_t v_hash_1774_, lean_object* v_s_1775_){
_start:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1775_);
v___x_1777_ = lean_nat_dec_le(v___x_1773_, v___x_1776_);
lean_dec(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v_toEnvExtension_1779_; lean_object* v_asyncMode_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1778_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1779_ = lean_ctor_get(v___x_1778_, 0);
v_asyncMode_1780_ = lean_ctor_get(v_toEnvExtension_1779_, 2);
v___x_1781_ = lean_box(1);
v___x_1782_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_1775_);
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1781_, v___x_1778_, v___x_1782_, v_asyncMode_1780_, v___x_1783_);
v___x_1785_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_hash_1774_, v___x_1784_);
lean_dec(v___x_1784_);
return v___x_1785_;
}
else
{
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object* v___x_1786_, lean_object* v_hash_1787_, lean_object* v_s_1788_){
_start:
{
uint64_t v_hash_boxed_1789_; uint8_t v_res_1790_; lean_object* v_r_1791_; 
v_hash_boxed_1789_ = lean_unbox_uint64(v_hash_1787_);
lean_dec_ref(v_hash_1787_);
v_res_1790_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1786_, v_hash_boxed_1789_, v_s_1788_);
lean_dec_ref(v_s_1788_);
lean_dec(v___x_1786_);
v_r_1791_ = lean_box(v_res_1790_);
return v_r_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object* v___x_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1792_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object* v___x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1796_, v___y_1797_);
lean_dec_ref(v___y_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object* v_snd_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_snd_1800_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1819_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1819_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1819_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_javascript_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v_javascript_1814_ = lean_ctor_get(v_a_1810_, 0);
lean_inc_ref(v_javascript_1814_);
lean_dec(v_a_1810_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_javascript_1814_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1815_);
v___x_1817_ = v___x_1812_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1809_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1809_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object* v_snd_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t v_hash_1838_, lean_object* v___x_1839_, lean_object* v_snap_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v_toEnvExtension_1844_; lean_object* v_asyncMode_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1843_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1844_ = lean_ctor_get(v___x_1843_, 0);
v_asyncMode_1845_ = lean_ctor_get(v_toEnvExtension_1844_, 2);
v___x_1846_ = lean_box(1);
v___x_1847_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1840_);
v___x_1848_ = lean_box(0);
v___x_1849_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1846_, v___x_1843_, v___x_1847_, v_asyncMode_1845_, v___x_1848_);
v___x_1850_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1849_, v_hash_1838_);
lean_dec(v___x_1849_);
if (lean_obj_tag(v___x_1850_) == 1)
{
lean_object* v_val_1851_; lean_object* v_snd_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; 
lean_dec_ref(v___x_1839_);
v_val_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v_snd_1852_ = lean_ctor_get(v_val_1851_, 1);
lean_inc(v_snd_1852_);
lean_dec(v_val_1851_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__2___boxed), 9, 1);
lean_closure_set(v___f_1853_, 0, v_snd_1852_);
v___x_1854_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1840_, v___f_1853_, v___y_1841_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
lean_dec(v___x_1850_);
lean_dec_ref(v_snap_1840_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1839_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object* v_hash_1856_, lean_object* v___x_1857_, lean_object* v_snap_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
uint64_t v_hash_boxed_1861_; lean_object* v_res_1862_; 
v_hash_boxed_1861_ = lean_unbox_uint64(v_hash_1856_);
lean_dec_ref(v_hash_1856_);
v_res_1862_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_boxed_1861_, v___x_1857_, v_snap_1858_, v___y_1859_);
lean_dec_ref(v___y_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource(lean_object* v_args_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; uint64_t v_hash_1870_; lean_object* v_pos_1871_; lean_object* v___x_1872_; 
v___x_1868_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1869_ = lean_st_ref_get(v___x_1868_);
v_hash_1870_ = lean_ctor_get_uint64(v_args_1865_, sizeof(void*)*1);
v_pos_1871_ = lean_ctor_get(v_args_1865_, 0);
lean_inc_ref(v_pos_1871_);
lean_dec_ref(v_args_1865_);
v___x_1872_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1869_, v_hash_1870_);
lean_dec(v___x_1869_);
if (lean_obj_tag(v___x_1872_) == 1)
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_pos_1871_);
v_val_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1884_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1884_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_snd_1877_; lean_object* v_javascript_1878_; lean_object* v___x_1880_; 
v_snd_1877_ = lean_ctor_get(v_val_1873_, 1);
lean_inc(v_snd_1877_);
lean_dec(v_val_1873_);
v_javascript_1878_ = lean_ctor_get(v_snd_1877_, 0);
lean_inc_ref(v_javascript_1878_);
lean_dec(v_snd_1877_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_javascript_1878_);
v___x_1880_ = v___x_1875_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_javascript_1878_);
v___x_1880_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_task_pure(v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
else
{
lean_object* v___x_1885_; lean_object* v_a_1886_; lean_object* v_toEditableDocumentCore_1887_; lean_object* v_meta_1888_; lean_object* v_text_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; 
lean_dec(v___x_1872_);
v___x_1885_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_1866_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v_toEditableDocumentCore_1887_ = lean_ctor_get(v_a_1886_, 0);
v_meta_1888_ = lean_ctor_get(v_toEditableDocumentCore_1887_, 0);
v_text_1889_ = lean_ctor_get(v_meta_1888_, 3);
v___x_1890_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1889_, v_pos_1871_);
v___x_1891_ = lean_box_uint64(v_hash_1870_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1892_, 0, v___x_1890_);
lean_closure_set(v___f_1892_, 1, v___x_1891_);
v___x_1893_ = 3;
v___x_1894_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_1895_ = lean_uint64_to_nat(v_hash_1870_);
v___x_1896_ = l_Nat_reprFast(v___x_1895_);
v___x_1897_ = lean_string_append(v___x_1894_, v___x_1896_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_1899_ = lean_string_append(v___x_1897_, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*1, v___x_1893_);
lean_inc_ref(v___x_1900_);
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1901_, 0, v___x_1900_);
v___x_1902_ = lean_box_uint64(v_hash_1870_);
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1903_, 0, v___x_1902_);
lean_closure_set(v___f_1903_, 1, v___x_1900_);
v___x_1904_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1886_, v___f_1892_, v___f_1901_, v___f_1903_, v_a_1866_);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object* v_args_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Widget_getWidgetSource(v_args_1905_, v_a_1906_);
lean_dec_ref(v_a_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object* v_00_u03b2_1909_, uint64_t v_k_1910_, lean_object* v_t_1911_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1910_, v_t_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object* v_00_u03b2_1913_, lean_object* v_k_1914_, lean_object* v_t_1915_){
_start:
{
uint64_t v_k_boxed_1916_; uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_k_boxed_1916_ = lean_unbox_uint64(v_k_1914_);
lean_dec_ref(v_k_1914_);
v_res_1917_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(v_00_u03b2_1913_, v_k_boxed_1916_, v_t_1915_);
lean_dec(v_t_1915_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_1919_, lean_object* v_i_1920_, lean_object* v_k_1921_){
_start:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = lean_array_get_size(v_keys_1919_);
v___x_1923_ = lean_nat_dec_lt(v_i_1920_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_dec(v_i_1920_);
return v___x_1923_;
}
else
{
lean_object* v_k_x27_1924_; uint8_t v___x_1925_; 
v_k_x27_1924_ = lean_array_fget_borrowed(v_keys_1919_, v_i_1920_);
v___x_1925_ = lean_name_eq(v_k_1921_, v_k_x27_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_unsigned_to_nat(1u);
v___x_1927_ = lean_nat_add(v_i_1920_, v___x_1926_);
lean_dec(v_i_1920_);
v_i_1920_ = v___x_1927_;
goto _start;
}
else
{
lean_dec(v_i_1920_);
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_1929_, lean_object* v_i_1930_, lean_object* v_k_1931_){
_start:
{
uint8_t v_res_1932_; lean_object* v_r_1933_; 
v_res_1932_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1929_, v_i_1930_, v_k_1931_);
lean_dec(v_k_1931_);
lean_dec_ref(v_keys_1929_);
v_r_1933_ = lean_box(v_res_1932_);
return v_r_1933_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_1934_, size_t v_x_1935_, lean_object* v_x_1936_){
_start:
{
if (lean_obj_tag(v_x_1934_) == 0)
{
lean_object* v_es_1937_; lean_object* v___x_1938_; size_t v___x_1939_; size_t v___x_1940_; lean_object* v_j_1941_; lean_object* v___x_1942_; 
v_es_1937_ = lean_ctor_get(v_x_1934_, 0);
v___x_1938_ = lean_box(2);
v___x_1939_ = ((size_t)31ULL);
v___x_1940_ = lean_usize_land(v_x_1935_, v___x_1939_);
v_j_1941_ = lean_usize_to_nat(v___x_1940_);
v___x_1942_ = lean_array_get_borrowed(v___x_1938_, v_es_1937_, v_j_1941_);
lean_dec(v_j_1941_);
switch(lean_obj_tag(v___x_1942_))
{
case 0:
{
lean_object* v_key_1943_; uint8_t v___x_1944_; 
v_key_1943_ = lean_ctor_get(v___x_1942_, 0);
v___x_1944_ = lean_name_eq(v_x_1936_, v_key_1943_);
return v___x_1944_;
}
case 1:
{
lean_object* v_node_1945_; size_t v___x_1946_; size_t v___x_1947_; 
v_node_1945_ = lean_ctor_get(v___x_1942_, 0);
v___x_1946_ = ((size_t)5ULL);
v___x_1947_ = lean_usize_shift_right(v_x_1935_, v___x_1946_);
v_x_1934_ = v_node_1945_;
v_x_1935_ = v___x_1947_;
goto _start;
}
default: 
{
uint8_t v___x_1949_; 
v___x_1949_ = 0;
return v___x_1949_;
}
}
}
else
{
lean_object* v_ks_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_ks_1950_ = lean_ctor_get(v_x_1934_, 0);
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_1950_, v___x_1951_, v_x_1936_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
size_t v_x_1060__boxed_1956_; uint8_t v_res_1957_; lean_object* v_r_1958_; 
v_x_1060__boxed_1956_ = lean_unbox_usize(v_x_1954_);
lean_dec(v_x_1954_);
v_res_1957_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1953_, v_x_1060__boxed_1956_, v_x_1955_);
lean_dec(v_x_1955_);
lean_dec_ref(v_x_1953_);
v_r_1958_ = lean_box(v_res_1957_);
return v_r_1958_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1959_; uint64_t v___x_1960_; 
v___x_1959_ = lean_unsigned_to_nat(1723u);
v___x_1960_ = lean_uint64_of_nat(v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1961_, lean_object* v_x_1962_){
_start:
{
uint64_t v___y_1964_; 
if (lean_obj_tag(v_x_1962_) == 0)
{
uint64_t v___x_1967_; 
v___x_1967_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_1964_ = v___x_1967_;
goto v___jp_1963_;
}
else
{
uint64_t v_hash_1968_; 
v_hash_1968_ = lean_ctor_get_uint64(v_x_1962_, sizeof(void*)*2);
v___y_1964_ = v_hash_1968_;
goto v___jp_1963_;
}
v___jp_1963_:
{
size_t v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = lean_uint64_to_usize(v___y_1964_);
v___x_1966_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1961_, v___x_1965_, v_x_1962_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1969_, lean_object* v_x_1970_){
_start:
{
uint8_t v_res_1971_; lean_object* v_r_1972_; 
v_res_1971_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1969_, v_x_1970_);
lean_dec(v_x_1970_);
lean_dec_ref(v_x_1969_);
v_r_1972_ = lean_box(v_res_1971_);
return v_r_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
lean_object* v_ks_1977_; lean_object* v_vs_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2002_; 
v_ks_1977_ = lean_ctor_get(v_x_1973_, 0);
v_vs_1978_ = lean_ctor_get(v_x_1973_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1973_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1980_ = v_x_1973_;
v_isShared_1981_ = v_isSharedCheck_2002_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_vs_1978_);
lean_inc(v_ks_1977_);
lean_dec(v_x_1973_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2002_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = lean_array_get_size(v_ks_1977_);
v___x_1983_ = lean_nat_dec_lt(v_x_1974_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_dec(v_x_1974_);
v___x_1984_ = lean_array_push(v_ks_1977_, v_x_1975_);
v___x_1985_ = lean_array_push(v_vs_1978_, v_x_1976_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_1985_);
lean_ctor_set(v___x_1980_, 0, v___x_1984_);
v___x_1987_ = v___x_1980_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v_k_x27_1989_; uint8_t v___x_1990_; 
v_k_x27_1989_ = lean_array_fget_borrowed(v_ks_1977_, v_x_1974_);
v___x_1990_ = lean_name_eq(v_x_1975_, v_k_x27_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1992_; 
if (v_isShared_1981_ == 0)
{
v___x_1992_ = v___x_1980_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_ks_1977_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_vs_1978_);
v___x_1992_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_nat_add(v_x_1974_, v___x_1993_);
lean_dec(v_x_1974_);
v_x_1973_ = v___x_1992_;
v_x_1974_ = v___x_1994_;
goto _start;
}
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = lean_array_fset(v_ks_1977_, v_x_1974_, v_x_1975_);
v___x_1998_ = lean_array_fset(v_vs_1978_, v_x_1974_, v_x_1976_);
lean_dec(v_x_1974_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_1998_);
lean_ctor_set(v___x_1980_, 0, v___x_1997_);
v___x_2000_ = v___x_1980_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_n_2003_, lean_object* v_k_2004_, lean_object* v_v_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_n_2003_, v___x_2006_, v_k_2004_, v_v_2005_);
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_x_2009_, size_t v_x_2010_, size_t v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2009_) == 0)
{
lean_object* v_es_2014_; size_t v___x_2015_; size_t v___x_2016_; lean_object* v_j_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_es_2014_ = lean_ctor_get(v_x_2009_, 0);
v___x_2015_ = ((size_t)31ULL);
v___x_2016_ = lean_usize_land(v_x_2010_, v___x_2015_);
v_j_2017_ = lean_usize_to_nat(v___x_2016_);
v___x_2018_ = lean_array_get_size(v_es_2014_);
v___x_2019_ = lean_nat_dec_lt(v_j_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_dec(v_j_2017_);
lean_dec(v_x_2013_);
lean_dec(v_x_2012_);
return v_x_2009_;
}
else
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2058_; 
lean_inc_ref(v_es_2014_);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2009_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_x_2009_, 0);
lean_dec(v_unused_2059_);
v___x_2021_ = v_x_2009_;
v_isShared_2022_ = v_isSharedCheck_2058_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_x_2009_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2058_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v_v_2023_; lean_object* v___x_2024_; lean_object* v_xs_x27_2025_; lean_object* v___y_2027_; 
v_v_2023_ = lean_array_fget(v_es_2014_, v_j_2017_);
v___x_2024_ = lean_box(0);
v_xs_x27_2025_ = lean_array_fset(v_es_2014_, v_j_2017_, v___x_2024_);
switch(lean_obj_tag(v_v_2023_))
{
case 0:
{
lean_object* v_key_2032_; lean_object* v_val_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2043_; 
v_key_2032_ = lean_ctor_get(v_v_2023_, 0);
v_val_2033_ = lean_ctor_get(v_v_2023_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_v_2023_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2035_ = v_v_2023_;
v_isShared_2036_ = v_isSharedCheck_2043_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_val_2033_);
lean_inc(v_key_2032_);
lean_dec(v_v_2023_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2043_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_name_eq(v_x_2012_, v_key_2032_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_del_object(v___x_2035_);
v___x_2038_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2032_, v_val_2033_, v_x_2012_, v_x_2013_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
v___y_2027_ = v___x_2039_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2041_; 
lean_dec(v_val_2033_);
lean_dec(v_key_2032_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_x_2013_);
lean_ctor_set(v___x_2035_, 0, v_x_2012_);
v___x_2041_ = v___x_2035_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_x_2012_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_x_2013_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
v___y_2027_ = v___x_2041_;
goto v___jp_2026_;
}
}
}
}
case 1:
{
lean_object* v_node_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2056_; 
v_node_2044_ = lean_ctor_get(v_v_2023_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_v_2023_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2046_ = v_v_2023_;
v_isShared_2047_ = v_isSharedCheck_2056_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_node_2044_);
lean_dec(v_v_2023_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2056_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
size_t v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2048_ = ((size_t)5ULL);
v___x_2049_ = lean_usize_shift_right(v_x_2010_, v___x_2048_);
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_x_2011_, v___x_2050_);
v___x_2052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_node_2044_, v___x_2049_, v___x_2051_, v_x_2012_, v_x_2013_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2052_);
v___x_2054_ = v___x_2046_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
v___y_2027_ = v___x_2054_;
goto v___jp_2026_;
}
}
}
default: 
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_x_2012_);
lean_ctor_set(v___x_2057_, 1, v_x_2013_);
v___y_2027_ = v___x_2057_;
goto v___jp_2026_;
}
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_array_fset(v_xs_x27_2025_, v_j_2017_, v___y_2027_);
lean_dec(v_j_2017_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2028_);
v___x_2030_ = v___x_2021_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_ks_2060_; lean_object* v_vs_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2081_; 
v_ks_2060_ = lean_ctor_get(v_x_2009_, 0);
v_vs_2061_ = lean_ctor_get(v_x_2009_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_x_2009_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2063_ = v_x_2009_;
v_isShared_2064_ = v_isSharedCheck_2081_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_vs_2061_);
lean_inc(v_ks_2060_);
lean_dec(v_x_2009_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2081_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_ks_2060_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_vs_2061_);
v___x_2066_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v_newNode_2067_; uint8_t v___y_2069_; size_t v___x_2075_; uint8_t v___x_2076_; 
v_newNode_2067_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v___x_2066_, v_x_2012_, v_x_2013_);
v___x_2075_ = ((size_t)7ULL);
v___x_2076_ = lean_usize_dec_le(v___x_2075_, v_x_2011_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2077_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2067_);
v___x_2078_ = lean_unsigned_to_nat(4u);
v___x_2079_ = lean_nat_dec_lt(v___x_2077_, v___x_2078_);
lean_dec(v___x_2077_);
v___y_2069_ = v___x_2079_;
goto v___jp_2068_;
}
else
{
v___y_2069_ = v___x_2076_;
goto v___jp_2068_;
}
v___jp_2068_:
{
if (v___y_2069_ == 0)
{
lean_object* v_ks_2070_; lean_object* v_vs_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_ks_2070_ = lean_ctor_get(v_newNode_2067_, 0);
lean_inc_ref(v_ks_2070_);
v_vs_2071_ = lean_ctor_get(v_newNode_2067_, 1);
lean_inc_ref(v_vs_2071_);
lean_dec_ref(v_newNode_2067_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0);
v___x_2074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_x_2011_, v_ks_2070_, v_vs_2071_, v___x_2072_, v___x_2073_);
lean_dec_ref(v_vs_2071_);
lean_dec_ref(v_ks_2070_);
return v___x_2074_;
}
else
{
return v_newNode_2067_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t v_depth_2082_, lean_object* v_keys_2083_, lean_object* v_vals_2084_, lean_object* v_i_2085_, lean_object* v_entries_2086_){
_start:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_array_get_size(v_keys_2083_);
v___x_2088_ = lean_nat_dec_lt(v_i_2085_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_dec(v_i_2085_);
return v_entries_2086_;
}
else
{
lean_object* v_k_2089_; lean_object* v_v_2090_; uint64_t v___y_2092_; 
v_k_2089_ = lean_array_fget_borrowed(v_keys_2083_, v_i_2085_);
v_v_2090_ = lean_array_fget_borrowed(v_vals_2084_, v_i_2085_);
if (lean_obj_tag(v_k_2089_) == 0)
{
uint64_t v___x_2103_; 
v___x_2103_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_2092_ = v___x_2103_;
goto v___jp_2091_;
}
else
{
uint64_t v_hash_2104_; 
v_hash_2104_ = lean_ctor_get_uint64(v_k_2089_, sizeof(void*)*2);
v___y_2092_ = v_hash_2104_;
goto v___jp_2091_;
}
v___jp_2091_:
{
size_t v_h_2093_; size_t v___x_2094_; lean_object* v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; size_t v_h_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_h_2093_ = lean_uint64_to_usize(v___y_2092_);
v___x_2094_ = ((size_t)5ULL);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = ((size_t)1ULL);
v___x_2097_ = lean_usize_sub(v_depth_2082_, v___x_2096_);
v___x_2098_ = lean_usize_mul(v___x_2094_, v___x_2097_);
v_h_2099_ = lean_usize_shift_right(v_h_2093_, v___x_2098_);
v___x_2100_ = lean_nat_add(v_i_2085_, v___x_2095_);
lean_dec(v_i_2085_);
lean_inc(v_v_2090_);
lean_inc(v_k_2089_);
v___x_2101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_entries_2086_, v_h_2099_, v_depth_2082_, v_k_2089_, v_v_2090_);
v_i_2085_ = v___x_2100_;
v_entries_2086_ = v___x_2101_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_depth_2105_, lean_object* v_keys_2106_, lean_object* v_vals_2107_, lean_object* v_i_2108_, lean_object* v_entries_2109_){
_start:
{
size_t v_depth_boxed_2110_; lean_object* v_res_2111_; 
v_depth_boxed_2110_ = lean_unbox_usize(v_depth_2105_);
lean_dec(v_depth_2105_);
v_res_2111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_boxed_2110_, v_keys_2106_, v_vals_2107_, v_i_2108_, v_entries_2109_);
lean_dec_ref(v_vals_2107_);
lean_dec_ref(v_keys_2106_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
size_t v_x_1204__boxed_2117_; size_t v_x_1205__boxed_2118_; lean_object* v_res_2119_; 
v_x_1204__boxed_2117_ = lean_unbox_usize(v_x_2113_);
lean_dec(v_x_2113_);
v_x_1205__boxed_2118_ = lean_unbox_usize(v_x_2114_);
lean_dec(v_x_2114_);
v_res_2119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2112_, v_x_1204__boxed_2117_, v_x_1205__boxed_2118_, v_x_2115_, v_x_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
uint64_t v___y_2124_; 
if (lean_obj_tag(v_x_2121_) == 0)
{
uint64_t v___x_2128_; 
v___x_2128_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_2124_ = v___x_2128_;
goto v___jp_2123_;
}
else
{
uint64_t v_hash_2129_; 
v_hash_2129_ = lean_ctor_get_uint64(v_x_2121_, sizeof(void*)*2);
v___y_2124_ = v_hash_2129_;
goto v___jp_2123_;
}
v___jp_2123_:
{
size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_uint64_to_usize(v___y_2124_);
v___x_2126_ = ((size_t)1ULL);
v___x_2127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2120_, v___x_2125_, v___x_2126_, v_x_2121_, v_x_2122_);
return v___x_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v___y_2130_){
_start:
{
lean_inc(v___y_2130_);
return v___y_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(v___y_2131_);
lean_dec(v___y_2131_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object* v_expireTime_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v_x_2134_);
lean_ctor_set(v___x_2135_, 1, v_expireTime_2133_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object* v_val_2136_, lean_object* v___f_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v___f_2137_);
v_a_2141_ = lean_ctor_get(v_x_2138_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v_x_2138_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v_x_2138_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 1);
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2172_; 
v_a_2149_ = lean_ctor_get(v_x_2138_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2151_ = v_x_2138_;
v_isShared_2152_ = v_isSharedCheck_2172_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v_x_2138_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2172_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v_objects_2154_; lean_object* v_expireTime_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2171_; 
v___x_2153_ = lean_st_ref_take(v_val_2136_);
v_objects_2154_ = lean_ctor_get(v___x_2153_, 0);
v_expireTime_2155_ = lean_ctor_get(v___x_2153_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2157_ = v___x_2153_;
v_isShared_2158_ = v_isSharedCheck_2171_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_expireTime_2155_);
lean_inc(v_objects_2154_);
lean_dec(v___x_2153_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2171_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___f_2159_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_2159_, 0, v_expireTime_2155_);
v___x_2160_ = l_Lean_Widget_instToJsonWidgetSource_toJson(v_a_2149_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v_objects_2154_);
lean_ctor_set(v___x_2157_, 0, v___x_2160_);
v___x_2162_ = v___x_2157_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_objects_2154_);
v___x_2162_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; lean_object* v_fst_2164_; lean_object* v_snd_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2163_ = l_Prod_map___redArg(v___f_2137_, v___f_2159_, v___x_2162_);
v_fst_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_fst_2164_);
v_snd_2165_ = lean_ctor_get(v___x_2163_, 1);
lean_inc(v_snd_2165_);
lean_dec_ref(v___x_2163_);
v___x_2166_ = lean_st_ref_set(v_val_2136_, v_snd_2165_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 0);
lean_ctor_set(v___x_2151_, 0, v_fst_2164_);
v___x_2168_ = v___x_2151_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_fst_2164_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object* v_val_2173_, lean_object* v___f_2174_, lean_object* v_x_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2173_, v___f_2174_, v_x_2175_, v___y_2176_);
lean_dec_ref(v___y_2176_);
lean_dec(v_val_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object* v_method_2186_, lean_object* v_handler_2187_, lean_object* v___f_2188_, uint64_t v_seshId_2189_, lean_object* v_j_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_rpcSessions_2193_; lean_object* v___x_2194_; 
v_rpcSessions_2193_ = lean_ctor_get(v___y_2191_, 0);
v___x_2194_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_2193_, v_seshId_2189_);
if (lean_obj_tag(v___x_2194_) == 1)
{
lean_object* v_val_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_val_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_val_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = lean_st_ref_get(v_val_2195_);
lean_dec(v___x_2196_);
lean_inc(v_j_2190_);
v___x_2197_ = l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(v_j_2190_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_val_2195_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v_handler_2187_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2218_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2218_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
uint8_t v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2202_ = 3;
v___x_2203_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_2204_ = 1;
v___x_2205_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2186_, v___x_2204_);
v___x_2206_ = lean_string_append(v___x_2203_, v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
v___x_2209_ = l_Lean_Json_compress(v_j_2190_);
v___x_2210_ = lean_string_append(v___x_2208_, v___x_2209_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
v___x_2213_ = lean_string_append(v___x_2212_, v_a_2198_);
lean_dec(v_a_2198_);
v___x_2214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*1, v___x_2202_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set_tag(v___x_2200_, 1);
lean_ctor_set(v___x_2200_, 0, v___x_2214_);
v___x_2216_ = v___x_2200_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2220_; 
lean_dec(v_j_2190_);
lean_dec(v_method_2186_);
v_a_2219_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2197_, 1);
lean_inc_ref(v___y_2191_);
v___x_2220_ = lean_apply_3(v_handler_2187_, v_a_2219_, v___y_2191_, lean_box(0));
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___f_2222_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2222_, 0, v_val_2195_);
lean_closure_set(v___f_2222_, 1, v___f_2188_);
v___x_2223_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_2221_, v___f_2222_, v___y_2191_);
return v___x_2223_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_val_2195_);
lean_dec_ref(v___f_2188_);
v_a_2224_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2220_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2220_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v___x_2194_);
lean_dec(v_j_2190_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v_handler_2187_);
lean_dec(v_method_2186_);
v___x_2232_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object* v_method_2234_, lean_object* v_handler_2235_, lean_object* v___f_2236_, lean_object* v_seshId_2237_, lean_object* v_j_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
uint64_t v_seshId_boxed_2241_; lean_object* v_res_2242_; 
v_seshId_boxed_2241_ = lean_unbox_uint64(v_seshId_2237_);
lean_dec_ref(v_seshId_2237_);
v_res_2242_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v_method_2234_, v_handler_2235_, v___f_2236_, v_seshId_boxed_2241_, v_j_2238_, v___y_2239_);
lean_dec_ref(v___y_2239_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_method_2244_, lean_object* v_handler_2245_){
_start:
{
lean_object* v___f_2246_; lean_object* v___f_2247_; 
v___f_2246_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed), 7, 3);
lean_closure_set(v___f_2247_, 0, v_method_2244_);
lean_closure_set(v___f_2247_, 1, v_handler_2245_);
lean_closure_set(v___f_2247_, 2, v___f_2246_);
return v___f_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object* v_method_2252_, lean_object* v_handler_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2289_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2289_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2289_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_errMsg_2265_; uint8_t v___x_2266_; 
v___x_2260_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_2261_ = 1;
lean_inc(v_method_2252_);
v___x_2262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2252_, v___x_2261_);
v___x_2263_ = lean_string_append(v___x_2260_, v___x_2262_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_2265_ = lean_string_append(v___x_2263_, v___x_2264_);
v___x_2266_ = lean_unbox(v_a_2256_);
lean_dec(v_a_2256_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_dec_ref(v_handler_2253_);
lean_dec(v_method_2252_);
v___x_2267_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_2268_ = lean_string_append(v_errMsg_2265_, v___x_2267_);
v___x_2269_ = lean_mk_io_user_error(v___x_2268_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set_tag(v___x_2258_, 1);
lean_ctor_set(v___x_2258_, 0, v___x_2269_);
v___x_2271_ = v___x_2258_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2273_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_2274_ = lean_st_ref_get(v___x_2273_);
v___x_2275_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2274_, v_method_2252_);
lean_dec(v___x_2274_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec_ref(v_errMsg_2265_);
v___x_2276_ = lean_st_ref_take(v___x_2273_);
lean_inc(v_method_2252_);
v___x_2277_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(v_method_2252_, v_handler_2253_);
v___x_2278_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2276_, v_method_2252_, v___x_2277_);
v___x_2279_ = lean_st_ref_set(v___x_2273_, v___x_2278_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2279_);
v___x_2281_ = v___x_2258_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec_ref(v_handler_2253_);
lean_dec(v_method_2252_);
v___x_2283_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_2284_ = lean_string_append(v_errMsg_2265_, v___x_2283_);
v___x_2285_ = lean_mk_io_user_error(v___x_2284_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set_tag(v___x_2258_, 1);
lean_ctor_set(v___x_2258_, 0, v___x_2285_);
v___x_2287_ = v___x_2258_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v_handler_2253_);
lean_dec(v_method_2252_);
v_a_2290_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2255_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2255_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2298_, lean_object* v_handler_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2298_, v_handler_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2310_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2311_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v___x_2309_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
return v_res_2313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2315_, v_x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
uint8_t v_res_2321_; lean_object* v_r_2322_; 
v_res_2321_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2318_, v_x_2319_, v_x_2320_);
lean_dec(v_x_2320_);
lean_dec_ref(v_x_2319_);
v_r_2322_ = lean_box(v_res_2321_);
return v_r_2322_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_2323_){
_start:
{
lean_inc_ref(v_x_2323_);
return v_x_2323_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2324_);
lean_dec_ref(v_x_2324_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_){
_start:
{
lean_inc_ref(v_x_2327_);
return v_x_2327_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2329_, lean_object* v_x_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b1_2329_, v_x_2330_, v___y_2331_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_x_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2334_, v_x_2335_, v_x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, size_t v_x_2340_, lean_object* v_x_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
size_t v_x_1735__boxed_2347_; uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_x_1735__boxed_2347_ = lean_unbox_usize(v_x_2345_);
lean_dec(v_x_2345_);
v_res_2348_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2343_, v_x_2344_, v_x_1735__boxed_2347_, v_x_2346_);
lean_dec(v_x_2346_);
lean_dec_ref(v_x_2344_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2350_, lean_object* v_x_2351_, size_t v_x_2352_, size_t v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2351_, v_x_2352_, v_x_2353_, v_x_2354_, v_x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2357_, lean_object* v_x_2358_, lean_object* v_x_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
size_t v_x_1746__boxed_2363_; size_t v_x_1747__boxed_2364_; lean_object* v_res_2365_; 
v_x_1746__boxed_2363_ = lean_unbox_usize(v_x_2359_);
lean_dec(v_x_2359_);
v_x_1747__boxed_2364_ = lean_unbox_usize(v_x_2360_);
lean_dec(v_x_2360_);
v_res_2365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_2357_, v_x_2358_, v_x_1746__boxed_2363_, v_x_1747__boxed_2364_, v_x_2361_, v_x_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2366_, lean_object* v_keys_2367_, lean_object* v_vals_2368_, lean_object* v_heq_2369_, lean_object* v_i_2370_, lean_object* v_k_2371_){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2367_, v_i_2370_, v_k_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_k_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2373_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_k_2378_);
lean_dec(v_k_2378_);
lean_dec_ref(v_vals_2375_);
lean_dec_ref(v_keys_2374_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_2381_, lean_object* v_n_2382_, lean_object* v_k_2383_, lean_object* v_v_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v_n_2382_, v_k_2383_, v_v_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2386_, size_t v_depth_2387_, lean_object* v_keys_2388_, lean_object* v_vals_2389_, lean_object* v_heq_2390_, lean_object* v_i_2391_, lean_object* v_entries_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2387_, v_keys_2388_, v_vals_2389_, v_i_2391_, v_entries_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2394_, lean_object* v_depth_2395_, lean_object* v_keys_2396_, lean_object* v_vals_2397_, lean_object* v_heq_2398_, lean_object* v_i_2399_, lean_object* v_entries_2400_){
_start:
{
size_t v_depth_boxed_2401_; lean_object* v_res_2402_; 
v_depth_boxed_2401_ = lean_unbox_usize(v_depth_2395_);
lean_dec(v_depth_2395_);
v_res_2402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(v_00_u03b2_2394_, v_depth_boxed_2401_, v_keys_2396_, v_vals_2397_, v_heq_2398_, v_i_2399_, v_entries_2400_);
lean_dec_ref(v_vals_2397_);
lean_dec_ref(v_keys_2396_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_x_2404_, v_x_2405_, v_x_2406_, v_x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(lean_object* v_x_2409_){
_start:
{
if (lean_obj_tag(v_x_2409_) == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___boxed(lean_object* v_x_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(v_x_2412_);
lean_dec_ref(v_x_2412_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object* v_t_2414_, lean_object* v_k_2415_){
_start:
{
if (lean_obj_tag(v_t_2414_) == 0)
{
lean_object* v_n_2416_; lean_object* v___x_2417_; 
v_n_2416_ = lean_ctor_get(v_t_2414_, 0);
lean_inc(v_n_2416_);
lean_dec_ref_known(v_t_2414_, 1);
v___x_2417_ = lean_apply_1(v_k_2415_, v_n_2416_);
return v___x_2417_;
}
else
{
lean_object* v_wi_2418_; lean_object* v___x_2419_; 
v_wi_2418_ = lean_ctor_get(v_t_2414_, 0);
lean_inc_ref(v_wi_2418_);
lean_dec_ref_known(v_t_2414_, 1);
v___x_2419_ = lean_apply_1(v_k_2415_, v_wi_2418_);
return v___x_2419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object* v_motive_2420_, lean_object* v_ctorIdx_2421_, lean_object* v_t_2422_, lean_object* v_h_2423_, lean_object* v_k_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2422_, v_k_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object* v_motive_2426_, lean_object* v_ctorIdx_2427_, lean_object* v_t_2428_, lean_object* v_h_2429_, lean_object* v_k_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(v_motive_2426_, v_ctorIdx_2427_, v_t_2428_, v_h_2429_, v_k_2430_);
lean_dec(v_ctorIdx_2427_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object* v_t_2432_, lean_object* v_global_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2432_, v_global_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object* v_motive_2435_, lean_object* v_t_2436_, lean_object* v_h_2437_, lean_object* v_global_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2436_, v_global_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object* v_t_2440_, lean_object* v_local_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2440_, v_local_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object* v_motive_2443_, lean_object* v_t_2444_, lean_object* v_h_2445_, lean_object* v_local_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2444_, v_local_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2448_, uint64_t v_k_2449_, lean_object* v_fallback_2450_){
_start:
{
if (lean_obj_tag(v_t_2448_) == 0)
{
lean_object* v_k_2451_; lean_object* v_v_2452_; lean_object* v_l_2453_; lean_object* v_r_2454_; uint64_t v___x_2455_; uint8_t v___x_2456_; 
v_k_2451_ = lean_ctor_get(v_t_2448_, 1);
v_v_2452_ = lean_ctor_get(v_t_2448_, 2);
v_l_2453_ = lean_ctor_get(v_t_2448_, 3);
v_r_2454_ = lean_ctor_get(v_t_2448_, 4);
v___x_2455_ = lean_unbox_uint64(v_k_2451_);
v___x_2456_ = lean_uint64_dec_lt(v_k_2449_, v___x_2455_);
if (v___x_2456_ == 0)
{
uint64_t v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = lean_unbox_uint64(v_k_2451_);
v___x_2458_ = lean_uint64_dec_eq(v_k_2449_, v___x_2457_);
if (v___x_2458_ == 0)
{
v_t_2448_ = v_r_2454_;
goto _start;
}
else
{
lean_inc(v_v_2452_);
return v_v_2452_;
}
}
else
{
v_t_2448_ = v_l_2453_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2450_);
return v_fallback_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2461_, lean_object* v_k_2462_, lean_object* v_fallback_2463_){
_start:
{
uint64_t v_k_boxed_2464_; lean_object* v_res_2465_; 
v_k_boxed_2464_ = lean_unbox_uint64(v_k_2462_);
lean_dec_ref(v_k_2462_);
v_res_2465_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2461_, v_k_boxed_2464_, v_fallback_2463_);
lean_dec(v_fallback_2463_);
lean_dec(v_t_2461_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_s_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v_fst_2468_; lean_object* v_snd_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2482_; 
v_fst_2468_ = lean_ctor_get(v_x_2467_, 0);
v_snd_2469_ = lean_ctor_get(v_x_2467_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_x_2467_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2471_ = v_x_2467_;
v_isShared_2472_ = v_isSharedCheck_2482_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_snd_2469_);
lean_inc(v_fst_2468_);
lean_dec(v_x_2467_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2482_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; uint64_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_snd_2469_);
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_unbox_uint64(v_fst_2468_);
v___x_2476_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_s_2466_, v___x_2475_, v___x_2474_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set_tag(v___x_2471_, 1);
lean_ctor_set(v___x_2471_, 1, v___x_2476_);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2478_ = v___x_2471_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
uint64_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_unbox_uint64(v_fst_2468_);
lean_dec(v_fst_2468_);
v___x_2480_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_2479_, v___x_2478_, v_s_2466_);
return v___x_2480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_x_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_a_2484_);
lean_inc_ref_n(v___x_2485_, 2);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
lean_ctor_set(v___x_2486_, 2, v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_x_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v_x_2487_, v_a_2488_);
lean_dec_ref(v_x_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v___y_2490_){
_start:
{
lean_inc(v___y_2490_);
return v___y_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v___y_2491_);
lean_dec(v___y_2491_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_));
v___x_2508_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2511_, lean_object* v_t_2512_, uint64_t v_k_2513_, lean_object* v_fallback_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2512_, v_k_2513_, v_fallback_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2516_, lean_object* v_t_2517_, lean_object* v_k_2518_, lean_object* v_fallback_2519_){
_start:
{
uint64_t v_k_boxed_2520_; lean_object* v_res_2521_; 
v_k_boxed_2520_ = lean_unbox_uint64(v_k_2518_);
lean_dec_ref(v_k_2518_);
v_res_2521_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(v_00_u03b4_2516_, v_t_2517_, v_k_boxed_2520_, v_fallback_2519_);
lean_dec(v_fallback_2519_);
lean_dec(v_t_2517_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(lean_object* v_as_x27_2522_, lean_object* v_b_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
if (lean_obj_tag(v_as_x27_2522_) == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_b_2523_);
return v___x_2529_;
}
else
{
lean_object* v_head_2530_; 
v_head_2530_ = lean_ctor_get(v_as_x27_2522_, 0);
if (lean_obj_tag(v_head_2530_) == 0)
{
lean_object* v_tail_2531_; lean_object* v_n_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_tail_2531_ = lean_ctor_get(v_as_x27_2522_, 1);
v_n_2532_ = lean_ctor_get(v_head_2530_, 0);
v___x_2533_ = lean_box(0);
lean_inc(v_n_2532_);
v___x_2534_ = l_Lean_mkConst(v_n_2532_, v___x_2533_);
v___x_2535_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v___x_2534_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_array_push(v_b_2523_, v_a_2536_);
v_as_x27_2522_ = v_tail_2531_;
v_b_2523_ = v___x_2537_;
goto _start;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v_b_2523_);
v_a_2539_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2535_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2535_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_tail_2547_; lean_object* v_wi_2548_; lean_object* v___x_2549_; 
v_tail_2547_ = lean_ctor_get(v_as_x27_2522_, 1);
v_wi_2548_ = lean_ctor_get(v_head_2530_, 0);
lean_inc_ref(v_wi_2548_);
v___x_2549_ = lean_array_push(v_b_2523_, v_wi_2548_);
v_as_x27_2522_ = v_tail_2547_;
v_b_2523_ = v___x_2549_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg___boxed(lean_object* v_as_x27_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2551_, v_b_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v_as_x27_2551_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(lean_object* v_init_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v_v_2566_; lean_object* v_l_2567_; lean_object* v_r_2568_; lean_object* v___x_2569_; 
v_v_2566_ = lean_ctor_get(v_x_2560_, 2);
v_l_2567_ = lean_ctor_get(v_x_2560_, 3);
v_r_2568_ = lean_ctor_get(v_x_2560_, 4);
v___x_2569_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2559_, v_l_2567_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v_a_2571_; lean_object* v___x_2572_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v_a_2571_ = lean_ctor_get(v_a_2570_, 0);
lean_inc(v_a_2571_);
lean_dec(v_a_2570_);
v___x_2572_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_v_2566_, v_a_2571_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v_init_2559_ = v_a_2573_;
v_x_2560_ = v_r_2568_;
goto _start;
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2572_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2572_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
return v___x_2569_;
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_init_2559_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1___boxed(lean_object* v_init_2585_, lean_object* v_x_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2585_, v_x_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v_x_2586_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets(lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v_env_2601_; lean_object* v___x_2602_; lean_object* v_ext_2603_; lean_object* v_toEnvExtension_2604_; lean_object* v_asyncMode_2605_; lean_object* v_ret_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2600_ = lean_st_ref_get(v_a_2598_);
v_env_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc_ref(v_env_2601_);
lean_dec(v___x_2600_);
v___x_2602_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v_ext_2603_ = lean_ctor_get(v___x_2602_, 1);
v_toEnvExtension_2604_ = lean_ctor_get(v_ext_2603_, 0);
v_asyncMode_2605_ = lean_ctor_get(v_toEnvExtension_2604_, 2);
v_ret_2606_ = ((lean_object*)(l_Lean_Widget_evalPanelWidgets___closed__0));
v___x_2607_ = lean_box(1);
v___x_2608_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2607_, v___x_2602_, v_env_2601_, v_asyncMode_2605_);
v___x_2609_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_ret_2606_, v___x_2608_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v___x_2608_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2618_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2618_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2618_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v_a_2614_; lean_object* v___x_2616_; 
v_a_2614_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_a_2614_);
lean_dec(v_a_2610_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_a_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
v_a_2619_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2609_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2609_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Widget_evalPanelWidgets(v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object* v_as_2633_, lean_object* v_as_x27_2634_, lean_object* v_b_2635_, lean_object* v_a_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2634_, v_b_2635_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object* v_as_2643_, lean_object* v_as_x27_2644_, lean_object* v_b_2645_, lean_object* v_a_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2643_, v_as_x27_2644_, v_b_2645_, v_a_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v_as_x27_2644_);
lean_dec(v_as_2643_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, uint64_t v_h_2656_, lean_object* v_n_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2658_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2659_ = lean_box_uint64(v_h_2656_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
lean_ctor_set(v___x_2660_, 1, v_n_2657_);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2653_, v_inst_2655_, v_inst_2654_, v___x_2658_, v___x_2660_, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_h_2666_, lean_object* v_n_2667_){
_start:
{
uint64_t v_h_boxed_2668_; lean_object* v_res_2669_; 
v_h_boxed_2668_ = lean_unbox_uint64(v_h_2666_);
lean_dec_ref(v_h_2666_);
v_res_2669_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2663_, v_inst_2664_, v_inst_2665_, v_h_boxed_2668_, v_n_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object* v_m_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, uint64_t v_h_2674_, lean_object* v_n_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2671_, v_inst_2672_, v_inst_2673_, v_h_2674_, v_n_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object* v_m_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_h_2681_, lean_object* v_n_2682_){
_start:
{
uint64_t v_h_boxed_2683_; lean_object* v_res_2684_; 
v_h_boxed_2683_ = lean_unbox_uint64(v_h_2681_);
lean_dec_ref(v_h_2681_);
v_res_2684_ = l_Lean_Widget_addPanelWidgetGlobal(v_m_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_h_boxed_2683_, v_n_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object* v_inst_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, uint64_t v_h_2688_, lean_object* v_n_2689_){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2691_ = lean_box_uint64(v_h_2688_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v_n_2689_);
v___x_2693_ = 2;
v___x_2694_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2685_, v_inst_2687_, v_inst_2686_, v___x_2690_, v___x_2692_, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_h_2698_, lean_object* v_n_2699_){
_start:
{
uint64_t v_h_boxed_2700_; lean_object* v_res_2701_; 
v_h_boxed_2700_ = lean_unbox_uint64(v_h_2698_);
lean_dec_ref(v_h_2698_);
v_res_2701_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2695_, v_inst_2696_, v_inst_2697_, v_h_boxed_2700_, v_n_2699_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, uint64_t v_h_2706_, lean_object* v_n_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2703_, v_inst_2704_, v_inst_2705_, v_h_2706_, v_n_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object* v_m_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_h_2713_, lean_object* v_n_2714_){
_start:
{
uint64_t v_h_boxed_2715_; lean_object* v_res_2716_; 
v_h_boxed_2715_ = lean_unbox_uint64(v_h_2713_);
lean_dec_ref(v_h_2713_);
v_res_2716_ = l_Lean_Widget_addPanelWidgetScoped(v_m_2709_, v_inst_2710_, v_inst_2711_, v_inst_2712_, v_h_boxed_2715_, v_n_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t v_x_2717_, uint64_t v_y_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_uint64_dec_lt(v_x_2717_, v_y_2718_);
if (v___x_2719_ == 0)
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_uint64_dec_eq(v_x_2717_, v_y_2718_);
if (v___x_2720_ == 0)
{
uint8_t v___x_2721_; 
v___x_2721_ = 2;
return v___x_2721_;
}
else
{
uint8_t v___x_2722_; 
v___x_2722_ = 1;
return v___x_2722_;
}
}
else
{
uint8_t v___x_2723_; 
v___x_2723_ = 0;
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object* v_x_2724_, lean_object* v_y_2725_){
_start:
{
uint64_t v_x_boxed_2726_; uint64_t v_y_boxed_2727_; uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_x_boxed_2726_ = lean_unbox_uint64(v_x_2724_);
lean_dec_ref(v_x_2724_);
v_y_boxed_2727_ = lean_unbox_uint64(v_y_2725_);
lean_dec_ref(v_y_2725_);
v_res_2728_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_boxed_2726_, v_y_boxed_2727_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object* v_wi_2730_, lean_object* v___f_2731_, lean_object* v_s_2732_){
_start:
{
uint64_t v_javascriptHash_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_javascriptHash_2733_ = lean_ctor_get_uint64(v_wi_2730_, sizeof(void*)*2);
v___x_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_wi_2730_);
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_box_uint64(v_javascriptHash_2733_);
lean_inc(v_s_2732_);
lean_inc_ref(v___f_2731_);
v___x_2737_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___f_2731_, v_s_2732_, v___x_2736_, v___x_2735_);
v___x_2738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2734_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_box_uint64(v_javascriptHash_2733_);
v___x_2740_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2731_, v___x_2739_, v___x_2738_, v_s_2732_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object* v___f_2741_, lean_object* v_env_2742_){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2744_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2743_, v_env_2742_, v___f_2741_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object* v_inst_2746_, lean_object* v_wi_2747_){
_start:
{
lean_object* v_modifyEnv_2748_; lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___x_2752_; 
v_modifyEnv_2748_ = lean_ctor_get(v_inst_2746_, 1);
lean_inc(v_modifyEnv_2748_);
lean_dec_ref(v_inst_2746_);
v___f_2749_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___f_2750_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2750_, 0, v_wi_2747_);
lean_closure_set(v___f_2750_, 1, v___f_2749_);
v___f_2751_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2751_, 0, v___f_2750_);
v___x_2752_ = lean_apply_1(v_modifyEnv_2748_, v___f_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object* v_m_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v_wi_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_Widget_addPanelWidgetLocal___redArg(v_inst_2755_, v_wi_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object* v_m_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_wi_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Widget_addPanelWidgetLocal(v_m_2758_, v_inst_2759_, v_inst_2760_, v_wi_2761_);
lean_dec_ref(v_inst_2759_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object* v___f_2763_, uint64_t v_h_2764_, lean_object* v_st_2765_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_box_uint64(v_h_2764_);
v___x_2767_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___f_2763_, v___x_2766_, v_st_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object* v___f_2768_, lean_object* v_h_2769_, lean_object* v_st_2770_){
_start:
{
uint64_t v_h_boxed_2771_; lean_object* v_res_2772_; 
v_h_boxed_2771_ = lean_unbox_uint64(v_h_2769_);
lean_dec_ref(v_h_2769_);
v_res_2772_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2768_, v_h_boxed_2771_, v_st_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object* v_inst_2773_, uint64_t v_h_2774_){
_start:
{
lean_object* v_modifyEnv_2775_; lean_object* v___f_2776_; lean_object* v___x_2777_; lean_object* v___f_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; 
v_modifyEnv_2775_ = lean_ctor_get(v_inst_2773_, 1);
lean_inc(v_modifyEnv_2775_);
lean_dec_ref(v_inst_2773_);
v___f_2776_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___x_2777_ = lean_box_uint64(v_h_2774_);
v___f_2778_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2778_, 0, v___f_2776_);
lean_closure_set(v___f_2778_, 1, v___x_2777_);
v___f_2779_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2779_, 0, v___f_2778_);
v___x_2780_ = lean_apply_1(v_modifyEnv_2775_, v___f_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object* v_inst_2781_, lean_object* v_h_2782_){
_start:
{
uint64_t v_h_boxed_2783_; lean_object* v_res_2784_; 
v_h_boxed_2783_ = lean_unbox_uint64(v_h_2782_);
lean_dec_ref(v_h_2782_);
v_res_2784_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2781_, v_h_boxed_2783_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget(lean_object* v_m_2785_, lean_object* v_inst_2786_, lean_object* v_inst_2787_, uint64_t v_h_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2787_, v_h_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object* v_m_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_h_2793_){
_start:
{
uint64_t v_h_boxed_2794_; lean_object* v_res_2795_; 
v_h_boxed_2794_ = lean_unbox_uint64(v_h_2793_);
lean_dec_ref(v_h_2793_);
v_res_2795_ = l_Lean_Widget_erasePanelWidget(v_m_2790_, v_inst_2791_, v_inst_2792_, v_h_boxed_2794_);
lean_dec_ref(v_inst_2791_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t v_hash_2796_, lean_object* v_props_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v_val_2805_; lean_object* v_env_2808_; lean_object* v___x_2809_; 
v___x_2801_ = lean_st_ref_get(v_a_2799_);
v___x_2802_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_2803_ = lean_st_ref_get(v___x_2802_);
v_env_2808_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_ref(v_env_2808_);
lean_dec(v___x_2801_);
v___x_2809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_2803_, v_hash_2796_);
lean_dec(v___x_2803_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; lean_object* v_toEnvExtension_2811_; lean_object* v_asyncMode_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2810_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_2811_ = lean_ctor_get(v___x_2810_, 0);
v_asyncMode_2812_ = lean_ctor_get(v_toEnvExtension_2811_, 2);
v___x_2813_ = lean_box(1);
v___x_2814_ = lean_box(0);
v___x_2815_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2813_, v___x_2810_, v_env_2808_, v_asyncMode_2812_, v___x_2814_);
v___x_2816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_2815_, v_hash_2796_);
lean_dec(v___x_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_props_2797_);
v___x_2817_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_2818_ = lean_uint64_to_nat(v_hash_2796_);
v___x_2819_ = l_Nat_reprFast(v___x_2818_);
v___x_2820_ = lean_string_append(v___x_2817_, v___x_2819_);
lean_dec_ref(v___x_2819_);
v___x_2821_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_2822_ = lean_string_append(v___x_2820_, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
v___x_2824_ = l_Lean_MessageData_ofFormat(v___x_2823_);
v___x_2825_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v___x_2824_, v_a_2798_, v_a_2799_);
return v___x_2825_;
}
else
{
lean_object* v_val_2826_; lean_object* v_fst_2827_; 
v_val_2826_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v___x_2816_, 1);
v_fst_2827_ = lean_ctor_get(v_val_2826_, 0);
lean_inc(v_fst_2827_);
lean_dec(v_val_2826_);
v_val_2805_ = v_fst_2827_;
goto v___jp_2804_;
}
}
else
{
lean_object* v_val_2828_; lean_object* v_fst_2829_; 
lean_dec_ref(v_env_2808_);
v_val_2828_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v___x_2809_, 1);
v_fst_2829_ = lean_ctor_get(v_val_2828_, 0);
lean_inc(v_fst_2829_);
lean_dec(v_val_2828_);
v_val_2805_ = v_fst_2829_;
goto v___jp_2804_;
}
v___jp_2804_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2806_, 0, v_val_2805_);
lean_ctor_set(v___x_2806_, 1, v_props_2797_);
lean_ctor_set_uint64(v___x_2806_, sizeof(void*)*2, v_hash_2796_);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object* v_hash_2830_, lean_object* v_props_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
uint64_t v_hash_boxed_2835_; lean_object* v_res_2836_; 
v_hash_boxed_2835_ = lean_unbox_uint64(v_hash_2830_);
lean_dec_ref(v_hash_2830_);
v_res_2836_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_boxed_2835_, v_props_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object* v_t_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; lean_object* v_infoState_2841_; uint8_t v_enabled_2842_; 
v___x_2840_ = lean_st_ref_get(v___y_2838_);
v_infoState_2841_ = lean_ctor_get(v___x_2840_, 7);
lean_inc_ref(v_infoState_2841_);
lean_dec(v___x_2840_);
v_enabled_2842_ = lean_ctor_get_uint8(v_infoState_2841_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2841_);
if (v_enabled_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v_t_2837_);
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; lean_object* v_infoState_2846_; lean_object* v_env_2847_; lean_object* v_nextMacroScope_2848_; lean_object* v_ngen_2849_; lean_object* v_auxDeclNGen_2850_; lean_object* v_traceState_2851_; lean_object* v_cache_2852_; lean_object* v_messages_2853_; lean_object* v_snapshotTasks_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2876_; 
v___x_2845_ = lean_st_ref_take(v___y_2838_);
v_infoState_2846_ = lean_ctor_get(v___x_2845_, 7);
v_env_2847_ = lean_ctor_get(v___x_2845_, 0);
v_nextMacroScope_2848_ = lean_ctor_get(v___x_2845_, 1);
v_ngen_2849_ = lean_ctor_get(v___x_2845_, 2);
v_auxDeclNGen_2850_ = lean_ctor_get(v___x_2845_, 3);
v_traceState_2851_ = lean_ctor_get(v___x_2845_, 4);
v_cache_2852_ = lean_ctor_get(v___x_2845_, 5);
v_messages_2853_ = lean_ctor_get(v___x_2845_, 6);
v_snapshotTasks_2854_ = lean_ctor_get(v___x_2845_, 8);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2856_ = v___x_2845_;
v_isShared_2857_ = v_isSharedCheck_2876_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_snapshotTasks_2854_);
lean_inc(v_infoState_2846_);
lean_inc(v_messages_2853_);
lean_inc(v_cache_2852_);
lean_inc(v_traceState_2851_);
lean_inc(v_auxDeclNGen_2850_);
lean_inc(v_ngen_2849_);
lean_inc(v_nextMacroScope_2848_);
lean_inc(v_env_2847_);
lean_dec(v___x_2845_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2876_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
uint8_t v_enabled_2858_; lean_object* v_assignment_2859_; lean_object* v_lazyAssignment_2860_; lean_object* v_trees_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2875_; 
v_enabled_2858_ = lean_ctor_get_uint8(v_infoState_2846_, sizeof(void*)*3);
v_assignment_2859_ = lean_ctor_get(v_infoState_2846_, 0);
v_lazyAssignment_2860_ = lean_ctor_get(v_infoState_2846_, 1);
v_trees_2861_ = lean_ctor_get(v_infoState_2846_, 2);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_infoState_2846_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2863_ = v_infoState_2846_;
v_isShared_2864_ = v_isSharedCheck_2875_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_trees_2861_);
lean_inc(v_lazyAssignment_2860_);
lean_inc(v_assignment_2859_);
lean_dec(v_infoState_2846_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2875_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2865_ = l_Lean_PersistentArray_push___redArg(v_trees_2861_, v_t_2837_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 2, v___x_2865_);
v___x_2867_ = v___x_2863_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_assignment_2859_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_lazyAssignment_2860_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v___x_2865_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, sizeof(void*)*3, v_enabled_2858_);
v___x_2867_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 7, v___x_2867_);
v___x_2869_ = v___x_2856_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_env_2847_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_nextMacroScope_2848_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_ngen_2849_);
lean_ctor_set(v_reuseFailAlloc_2873_, 3, v_auxDeclNGen_2850_);
lean_ctor_set(v_reuseFailAlloc_2873_, 4, v_traceState_2851_);
lean_ctor_set(v_reuseFailAlloc_2873_, 5, v_cache_2852_);
lean_ctor_set(v_reuseFailAlloc_2873_, 6, v_messages_2853_);
lean_ctor_set(v_reuseFailAlloc_2873_, 7, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2873_, 8, v_snapshotTasks_2854_);
v___x_2869_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = lean_st_ref_set(v___y_2838_, v___x_2869_);
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2877_, v___y_2878_);
lean_dec(v___y_2878_);
return v_res_2880_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_unsigned_to_nat(32u);
v___x_2882_ = lean_mk_empty_array_with_capacity(v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2884_ = ((size_t)5ULL);
v___x_2885_ = lean_unsigned_to_nat(0u);
v___x_2886_ = lean_unsigned_to_nat(32u);
v___x_2887_ = lean_mk_empty_array_with_capacity(v___x_2886_);
v___x_2888_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0);
v___x_2889_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___x_2887_);
lean_ctor_set(v___x_2889_, 2, v___x_2885_);
lean_ctor_set(v___x_2889_, 3, v___x_2885_);
lean_ctor_set_usize(v___x_2889_, 4, v___x_2884_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object* v_t_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; lean_object* v_infoState_2895_; uint8_t v_enabled_2896_; 
v___x_2894_ = lean_st_ref_get(v___y_2892_);
v_infoState_2895_ = lean_ctor_get(v___x_2894_, 7);
lean_inc_ref(v_infoState_2895_);
lean_dec(v___x_2894_);
v_enabled_2896_ = lean_ctor_get_uint8(v_infoState_2895_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2895_);
if (v_enabled_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec_ref(v_t_2890_);
v___x_2897_ = lean_box(0);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1);
v___x_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_t_2890_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v___x_2900_, v___y_2892_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object* v_t_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t v_hash_2907_, lean_object* v_props_2908_, lean_object* v_stx_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2907_, v_props_2908_, v_a_2910_, v_a_2911_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_a_2914_);
lean_ctor_set(v___x_2915_, 1, v_stx_2909_);
v___x_2916_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
v___x_2917_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v___x_2916_, v_a_2910_, v_a_2911_);
return v___x_2917_;
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_stx_2909_);
v_a_2918_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2913_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2913_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object* v_hash_2926_, lean_object* v_props_2927_, lean_object* v_stx_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
uint64_t v_hash_boxed_2932_; lean_object* v_res_2933_; 
v_hash_boxed_2932_ = lean_unbox_uint64(v_hash_2926_);
lean_dec_ref(v_hash_2926_);
v_res_2933_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_boxed_2932_, v_props_2927_, v_stx_2928_, v_a_2929_, v_a_2930_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object* v_t_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2934_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object* v_t_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object* v_x_2950_){
_start:
{
lean_object* v_name_2951_; lean_object* v_javascript_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2972_; 
v_name_2951_ = lean_ctor_get(v_x_2950_, 0);
v_javascript_2952_ = lean_ctor_get(v_x_2950_, 1);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_x_2950_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2954_ = v_x_2950_;
v_isShared_2955_ = v_isSharedCheck_2972_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_javascript_2952_);
lean_inc(v_name_2951_);
lean_dec(v_x_2950_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2972_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2956_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_2957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_name_2951_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2957_);
lean_ctor_set(v___x_2954_, 0, v___x_2956_);
v___x_2959_ = v___x_2954_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_2963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_javascript_2952_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2960_);
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___x_2960_);
v___x_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2961_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_2969_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_2967_, v___x_2968_);
v___x_2970_ = l_Lean_Json_mkObj(v___x_2969_);
lean_dec(v___x_2969_);
return v___x_2970_;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = 1;
v___x_2981_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_2982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2981_, v___x_2980_);
return v___x_2982_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_2984_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2);
v___x_2985_ = lean_string_append(v___x_2984_, v___x_2983_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = 1;
v___x_2989_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4));
v___x_2990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2989_, v___x_2988_);
return v___x_2990_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5);
v___x_2992_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2993_ = lean_string_append(v___x_2992_, v___x_2991_);
return v___x_2993_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2995_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6);
v___x_2996_ = lean_string_append(v___x_2995_, v___x_2994_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = 1;
v___x_3000_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8));
v___x_3001_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3000_, v___x_2999_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9);
v___x_3003_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_3004_ = lean_string_append(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_3006_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10);
v___x_3007_ = lean_string_append(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object* v_json_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
lean_inc(v_json_3008_);
v___x_3010_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3008_, v___x_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_json_3008_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3020_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3020_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3015_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7);
v___x_3016_ = lean_string_append(v___x_3015_, v_a_3011_);
lean_dec(v_a_3011_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3016_);
v___x_3018_ = v___x_3013_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v_json_3008_);
v_a_3021_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3010_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3010_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set_tag(v___x_3023_, 0);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_a_3029_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3030_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_3031_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3008_, v___x_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_3029_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3041_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3041_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3036_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11);
v___x_3037_ = lean_string_append(v___x_3036_, v_a_3032_);
lean_dec(v_a_3032_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3037_);
v___x_3039_ = v___x_3034_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_3029_);
v_a_3042_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3031_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3031_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
lean_ctor_set_tag(v___x_3044_, 0);
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3058_; 
v_a_3050_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3052_ = v___x_3031_;
v_isShared_3053_ = v_isSharedCheck_3058_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3031_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3058_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v_a_3029_);
lean_ctor_set(v___x_3054_, 1, v_a_3050_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3054_);
v___x_3056_ = v___x_3052_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object* v_uwd_3061_){
_start:
{
lean_object* v_javascript_3062_; uint64_t v___x_3063_; lean_object* v___x_3064_; 
v_javascript_3062_ = lean_ctor_get(v_uwd_3061_, 1);
v___x_3063_ = lean_string_hash(v_javascript_3062_);
lean_inc_ref(v_javascript_3062_);
v___x_3064_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3064_, 0, v_javascript_3062_);
lean_ctor_set_uint64(v___x_3064_, sizeof(void*)*1, v___x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object* v_uwd_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(v_uwd_3065_);
lean_dec_ref(v_uwd_3065_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object* v_____do__lift_3069_, lean_object* v_id_3070_, lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v___x_3073_, lean_object* v_____do__lift_3074_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3076_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_3069_, v_____do__lift_3074_, v___x_3075_, v_id_3070_);
v___x_3077_ = l_Lean_ofExcept___redArg(v_inst_3071_, v_inst_3072_, v___x_3073_, v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object* v_____do__lift_3078_, lean_object* v_id_3079_, lean_object* v_inst_3080_, lean_object* v_inst_3081_, lean_object* v___x_3082_, lean_object* v_____do__lift_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(v_____do__lift_3078_, v_id_3079_, v_inst_3080_, v_inst_3081_, v___x_3082_, v_____do__lift_3083_);
lean_dec_ref(v_____do__lift_3083_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object* v_id_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v___x_3088_, lean_object* v_toBind_3089_, lean_object* v_inst_3090_, lean_object* v_____do__lift_3091_){
_start:
{
lean_object* v___f_3092_; lean_object* v___x_3093_; 
v___f_3092_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_3092_, 0, v_____do__lift_3091_);
lean_closure_set(v___f_3092_, 1, v_id_3085_);
lean_closure_set(v___f_3092_, 2, v_inst_3086_);
lean_closure_set(v___f_3092_, 3, v_inst_3087_);
lean_closure_set(v___f_3092_, 4, v___x_3088_);
v___x_3093_ = lean_apply_4(v_toBind_3089_, lean_box(0), lean_box(0), v_inst_3090_, v___f_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object* v_inst_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_id_3099_){
_start:
{
lean_object* v_toBind_3100_; lean_object* v_getEnv_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; 
v_toBind_3100_ = lean_ctor_get(v_inst_3095_, 1);
lean_inc_n(v_toBind_3100_, 2);
v_getEnv_3101_ = lean_ctor_get(v_inst_3096_, 0);
lean_inc(v_getEnv_3101_);
lean_dec_ref(v_inst_3096_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0));
v___f_3103_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3103_, 0, v_id_3099_);
lean_closure_set(v___f_3103_, 1, v_inst_3095_);
lean_closure_set(v___f_3103_, 2, v_inst_3098_);
lean_closure_set(v___f_3103_, 3, v___x_3102_);
lean_closure_set(v___f_3103_, 4, v_toBind_3100_);
lean_closure_set(v___f_3103_, 5, v_inst_3097_);
v___x_3104_ = lean_apply_4(v_toBind_3100_, lean_box(0), lean_box(0), v_getEnv_3101_, v___f_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object* v_m_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_inst_3109_, lean_object* v_id_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(v_inst_3106_, v_inst_3107_, v_inst_3108_, v_inst_3109_, v_id_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object* v_text_3112_, lean_object* v_hoverLine_3113_, lean_object* v_x_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_){
_start:
{
if (lean_obj_tag(v_x_3115_) == 9)
{
lean_object* v_i_3117_; lean_object* v___x_3118_; 
v_i_3117_ = lean_ctor_get(v_x_3115_, 0);
v___x_3118_ = l_Lean_Elab_Info_pos_x3f(v_x_3115_);
if (lean_obj_tag(v___x_3118_) == 1)
{
lean_object* v_val_3119_; lean_object* v___x_3120_; 
v_val_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3120_ = l_Lean_Elab_Info_tailPos_x3f(v_x_3115_);
if (lean_obj_tag(v___x_3120_) == 1)
{
lean_object* v_val_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3136_; 
v_val_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3136_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_val_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3136_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v_line_3126_; uint8_t v___x_3127_; 
lean_inc_ref(v_text_3112_);
v___x_3125_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3112_, v_val_3119_);
lean_dec(v_val_3119_);
v_line_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_line_3126_);
lean_dec_ref(v___x_3125_);
v___x_3127_ = lean_nat_dec_le(v_line_3126_, v_hoverLine_3113_);
lean_dec(v_line_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
lean_del_object(v___x_3123_);
lean_dec(v_val_3121_);
lean_dec_ref(v_text_3112_);
v___x_3128_ = lean_box(0);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v_line_3130_; uint8_t v___x_3131_; 
v___x_3129_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3112_, v_val_3121_);
lean_dec(v_val_3121_);
v_line_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_line_3130_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = lean_nat_dec_le(v_hoverLine_3113_, v_line_3130_);
lean_dec(v_line_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
lean_del_object(v___x_3123_);
v___x_3132_ = lean_box(0);
return v___x_3132_;
}
else
{
lean_object* v___x_3134_; 
lean_inc_ref(v_i_3117_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v_i_3117_);
v___x_3134_ = v___x_3123_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_i_3117_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_object* v___x_3137_; 
lean_dec(v___x_3120_);
lean_dec(v_val_3119_);
lean_dec_ref(v_text_3112_);
v___x_3137_ = lean_box(0);
return v___x_3137_;
}
}
else
{
lean_object* v___x_3138_; 
lean_dec(v___x_3118_);
lean_dec_ref(v_text_3112_);
v___x_3138_ = lean_box(0);
return v___x_3138_;
}
}
else
{
lean_object* v___x_3139_; 
lean_dec_ref(v_text_3112_);
v___x_3139_ = lean_box(0);
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object* v_text_3140_, lean_object* v_hoverLine_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_, lean_object* v_x_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Widget_widgetInfosAt_x3f___lam__0(v_text_3140_, v_hoverLine_3141_, v_x_3142_, v_x_3143_, v_x_3144_);
lean_dec_ref(v_x_3144_);
lean_dec_ref(v_x_3143_);
lean_dec_ref(v_x_3142_);
lean_dec(v_hoverLine_3141_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object* v_text_3146_, lean_object* v_t_3147_, lean_object* v_hoverLine_3148_){
_start:
{
lean_object* v___f_3149_; lean_object* v___x_3150_; 
v___f_3149_ = lean_alloc_closure((void*)(l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_3149_, 0, v_text_3146_);
lean_closure_set(v___f_3149_, 1, v_hoverLine_3148_);
v___x_3150_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3149_, v_t_3147_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object* v_j_3151_, lean_object* v_k_3152_){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = l_Lean_Json_getObjValD(v_j_3151_, v_k_3152_);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object* v_j_3155_, lean_object* v_k_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_j_3155_, v_k_3156_);
lean_dec_ref(v_k_3156_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object* v_x_3160_){
_start:
{
if (lean_obj_tag(v_x_3160_) == 0)
{
lean_object* v___x_3161_; 
v___x_3161_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0));
return v___x_3161_;
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_x_3160_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object* v_j_3164_, lean_object* v_k_3165_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = l_Lean_Json_getObjValD(v_j_3164_, v_k_3165_);
v___x_3167_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object* v_j_3168_, lean_object* v_k_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_j_3168_, v_k_3169_);
lean_dec_ref(v_k_3169_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object* v_json_3175_){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_a_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v_a_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3198_; 
v___x_3176_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc_n(v_json_3175_, 4);
v___x_3177_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3175_, v___x_3176_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
v___x_3179_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3180_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3175_, v___x_3179_);
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref(v___x_3180_);
v___x_3182_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3183_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3175_, v___x_3182_);
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3183_);
v___x_3185_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3186_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3175_, v___x_3185_);
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref(v___x_3186_);
v___x_3188_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3189_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3175_, v___x_3188_);
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3194_, 0, v_a_3178_);
lean_ctor_set(v___x_3194_, 1, v_a_3181_);
lean_ctor_set(v___x_3194_, 2, v_a_3184_);
lean_ctor_set(v___x_3194_, 3, v_a_3187_);
lean_ctor_set(v___x_3194_, 4, v_a_3190_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3194_);
v___x_3196_ = v___x_3192_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(lean_object* v_k_3201_, lean_object* v_x_3202_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v_k_3201_);
v___x_3203_ = lean_box(0);
return v___x_3203_;
}
else
{
lean_object* v_val_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_val_3204_ = lean_ctor_get(v_x_3202_, 0);
lean_inc(v_val_3204_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v_k_3201_);
lean_ctor_set(v___x_3205_, 1, v_val_3204_);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0___boxed(lean_object* v_k_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v_k_3208_, v_x_3209_);
lean_dec(v_x_3209_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(lean_object* v_x_3211_){
_start:
{
lean_object* v_id_3212_; lean_object* v_javascriptHash_3213_; lean_object* v_props_3214_; lean_object* v_range_x3f_3215_; lean_object* v_name_x3f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_id_3212_ = lean_ctor_get(v_x_3211_, 0);
v_javascriptHash_3213_ = lean_ctor_get(v_x_3211_, 1);
v_props_3214_ = lean_ctor_get(v_x_3211_, 2);
v_range_x3f_3215_ = lean_ctor_get(v_x_3211_, 3);
v_name_x3f_3216_ = lean_ctor_get(v_x_3211_, 4);
v___x_3217_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_id_3212_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v_id_3212_);
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_javascriptHash_3213_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v_javascriptHash_3213_);
v___x_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3219_);
v___x_3224_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_props_3214_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v_props_3214_);
v___x_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v___x_3219_);
v___x_3227_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3228_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v___x_3227_, v_range_x3f_3215_);
v___x_3229_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3230_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v___x_3229_, v_name_x3f_3216_);
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3219_);
v___x_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3228_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3226_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3223_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3220_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3237_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3235_, v___x_3236_);
v___x_3238_ = l_Lean_Json_mkObj(v___x_3237_);
lean_dec(v___x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38____boxed(lean_object* v_x_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(v_x_3239_);
lean_dec_ref(v_x_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_toWidgetInstance_3245_; lean_object* v_range_x3f_3246_; lean_object* v_name_x3f_3247_; lean_object* v_id_3248_; uint64_t v_javascriptHash_3249_; lean_object* v_props_3250_; lean_object* v___x_3251_; lean_object* v_fst_3252_; lean_object* v_snd_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3293_; 
v_toWidgetInstance_3245_ = lean_ctor_get(v_a_3243_, 0);
lean_inc_ref(v_toWidgetInstance_3245_);
v_range_x3f_3246_ = lean_ctor_get(v_a_3243_, 1);
lean_inc(v_range_x3f_3246_);
v_name_x3f_3247_ = lean_ctor_get(v_a_3243_, 2);
lean_inc(v_name_x3f_3247_);
lean_dec_ref(v_a_3243_);
v_id_3248_ = lean_ctor_get(v_toWidgetInstance_3245_, 0);
lean_inc(v_id_3248_);
v_javascriptHash_3249_ = lean_ctor_get_uint64(v_toWidgetInstance_3245_, sizeof(void*)*2);
v_props_3250_ = lean_ctor_get(v_toWidgetInstance_3245_, 1);
lean_inc_ref(v_props_3250_);
lean_dec_ref(v_toWidgetInstance_3245_);
v___x_3251_ = lean_apply_1(v_props_3250_, v_a_3244_);
v_fst_3252_ = lean_ctor_get(v___x_3251_, 0);
v_snd_3253_ = lean_ctor_get(v___x_3251_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3255_ = v___x_3251_;
v_isShared_3256_ = v_isSharedCheck_3293_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_snd_3253_);
lean_inc(v_fst_3252_);
lean_dec(v___x_3251_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3293_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___y_3263_; lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v_fst_3272_; 
v___x_3257_ = 1;
v___x_3258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3248_, v___x_3257_);
v___x_3259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
v___x_3260_ = lean_uint64_to_nat(v_javascriptHash_3249_);
v___x_3261_ = l_Lean_bignumToJson(v___x_3260_);
if (lean_obj_tag(v_range_x3f_3246_) == 0)
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_box(0);
v_fst_3272_ = v___x_3283_;
goto v___jp_3271_;
}
else
{
lean_object* v_val_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3292_; 
v_val_3284_ = lean_ctor_get(v_range_x3f_3246_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_range_x3f_3246_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3286_ = v_range_x3f_3246_;
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_val_3284_);
lean_dec(v_range_x3f_3246_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_3284_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3288_);
v___x_3290_ = v___x_3286_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
v_fst_3272_ = v___x_3290_;
goto v___jp_3271_;
}
}
}
v___jp_3262_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3259_);
lean_ctor_set(v___x_3266_, 1, v___x_3261_);
lean_ctor_set(v___x_3266_, 2, v_fst_3252_);
lean_ctor_set(v___x_3266_, 3, v___y_3263_);
lean_ctor_set(v___x_3266_, 4, v_fst_3264_);
v___x_3267_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(v___x_3266_);
lean_dec_ref_known(v___x_3266_, 5);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 1, v_snd_3265_);
lean_ctor_set(v___x_3255_, 0, v___x_3267_);
v___x_3269_ = v___x_3255_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_snd_3265_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
v___jp_3271_:
{
if (lean_obj_tag(v_name_x3f_3247_) == 0)
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_box(0);
v___y_3263_ = v_fst_3272_;
v_fst_3264_ = v___x_3273_;
v_snd_3265_ = v_snd_3253_;
goto v___jp_3262_;
}
else
{
lean_object* v_val_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3282_; 
v_val_3274_ = lean_ctor_get(v_name_x3f_3247_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_name_x3f_3247_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3276_ = v_name_x3f_3247_;
v_isShared_3277_ = v_isSharedCheck_3282_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_val_3274_);
lean_dec(v_name_x3f_3247_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3282_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3278_, 0, v_val_3274_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3278_);
v___x_3280_ = v___x_3276_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
v___y_3263_ = v_fst_3272_;
v_fst_3264_ = v___x_3280_;
v_snd_3265_ = v_snd_3253_;
goto v___jp_3262_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_props_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_props_3294_);
lean_ctor_set(v___x_3296_, 1, v___y_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(v_j_3297_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v_id_3308_; lean_object* v_javascriptHash_3309_; lean_object* v_props_3310_; lean_object* v_range_x3f_3311_; lean_object* v_name_x3f_3312_; lean_object* v___x_3313_; 
v_a_3307_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3298_, 1);
v_id_3308_ = lean_ctor_get(v_a_3307_, 0);
lean_inc(v_id_3308_);
v_javascriptHash_3309_ = lean_ctor_get(v_a_3307_, 1);
lean_inc(v_javascriptHash_3309_);
v_props_3310_ = lean_ctor_get(v_a_3307_, 2);
lean_inc(v_props_3310_);
v_range_x3f_3311_ = lean_ctor_get(v_a_3307_, 3);
lean_inc(v_range_x3f_3311_);
v_name_x3f_3312_ = lean_ctor_get(v_a_3307_, 4);
lean_inc(v_name_x3f_3312_);
lean_dec(v_a_3307_);
v___x_3313_ = l_Lean_Name_fromJson_x3f(v_id_3308_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_name_x3f_3312_);
lean_dec(v_range_x3f_3311_);
lean_dec(v_props_3310_);
lean_dec(v_javascriptHash_3309_);
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3323_; 
v_a_3322_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3323_ = l_Lean_UInt64_fromJson_x3f(v_javascriptHash_3309_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v_a_3322_);
lean_dec(v_name_x3f_3312_);
lean_dec(v_range_x3f_3311_);
lean_dec(v_props_3310_);
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3386_; 
v_a_3332_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3334_ = v___x_3323_;
v_isShared_3335_ = v_isSharedCheck_3386_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3323_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3386_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___f_3336_; lean_object* v___y_3338_; lean_object* v_____do__lift_3339_; lean_object* v_____do__lift_3347_; 
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_), 2, 1);
lean_closure_set(v___f_3336_, 0, v_props_3310_);
if (lean_obj_tag(v_range_x3f_3311_) == 0)
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_box(0);
v_____do__lift_3347_ = v___x_3367_;
goto v___jp_3346_;
}
else
{
lean_object* v_val_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3385_; 
v_val_3368_ = lean_ctor_get(v_range_x3f_3311_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_range_x3f_3311_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3370_ = v_range_x3f_3311_;
v_isShared_3371_ = v_isSharedCheck_3385_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_val_3368_);
lean_dec(v_range_x3f_3311_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3385_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_3368_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_del_object(v___x_3370_);
lean_dec_ref(v___f_3336_);
lean_del_object(v___x_3334_);
lean_dec(v_a_3332_);
lean_dec(v_a_3322_);
lean_dec(v_name_x3f_3312_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; 
v_a_3381_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3372_, 1);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v_a_3381_);
v___x_3383_ = v___x_3370_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
v_____do__lift_3347_ = v___x_3383_;
goto v___jp_3346_;
}
}
}
}
v___jp_3337_:
{
lean_object* v___x_3340_; uint64_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3340_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3340_, 0, v_a_3322_);
lean_ctor_set(v___x_3340_, 1, v___f_3336_);
v___x_3341_ = lean_unbox_uint64(v_a_3332_);
lean_dec(v_a_3332_);
lean_ctor_set_uint64(v___x_3340_, sizeof(void*)*2, v___x_3341_);
v___x_3342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___y_3338_);
lean_ctor_set(v___x_3342_, 2, v_____do__lift_3339_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3342_);
v___x_3344_ = v___x_3334_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
v___jp_3346_:
{
if (lean_obj_tag(v_name_x3f_3312_) == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_box(0);
v___y_3338_ = v_____do__lift_3347_;
v_____do__lift_3339_ = v___x_3348_;
goto v___jp_3337_;
}
else
{
lean_object* v_val_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3366_; 
v_val_3349_ = lean_ctor_get(v_name_x3f_3312_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_name_x3f_3312_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3351_ = v_name_x3f_3312_;
v_isShared_3352_ = v_isSharedCheck_3366_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_val_3349_);
lean_dec(v_name_x3f_3312_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3366_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Json_getStr_x3f(v_val_3349_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_del_object(v___x_3351_);
lean_dec(v_____do__lift_3347_);
lean_dec_ref(v___f_3336_);
lean_del_object(v___x_3334_);
lean_dec(v_a_3332_);
lean_dec(v_a_3322_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; 
v_a_3362_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3353_, 1);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v_a_3362_);
v___x_3364_ = v___x_3351_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
v___y_3338_ = v_____do__lift_3347_;
v_____do__lift_3339_ = v___x_3364_;
goto v___jp_3337_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3387_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object* v_j_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3390_, v_a_3391_);
lean_dec_ref(v_a_3391_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object* v_json_3400_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v___x_3401_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3402_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3400_, v___x_3401_);
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(lean_object* v_x_3413_){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3414_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v_x_3413_);
v___x_3416_ = lean_box(0);
v___x_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___x_3416_);
v___x_3419_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3420_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3418_, v___x_3419_);
v___x_3421_ = l_Lean_Json_mkObj(v___x_3420_);
lean_dec(v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t v_sz_3424_, size_t v_i_3425_, lean_object* v_bs_3426_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_usize_dec_lt(v_i_3425_, v_sz_3424_);
if (v___x_3427_ == 0)
{
return v_bs_3426_;
}
else
{
lean_object* v_v_3428_; lean_object* v___x_3429_; lean_object* v_bs_x27_3430_; size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v_v_3428_ = lean_array_uget(v_bs_3426_, v_i_3425_);
v___x_3429_ = lean_unsigned_to_nat(0u);
v_bs_x27_3430_ = lean_array_uset(v_bs_3426_, v_i_3425_, v___x_3429_);
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3425_, v___x_3431_);
v___x_3433_ = lean_array_uset(v_bs_x27_3430_, v_i_3425_, v_v_3428_);
v_i_3425_ = v___x_3432_;
v_bs_3426_ = v___x_3433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object* v_sz_3435_, lean_object* v_i_3436_, lean_object* v_bs_3437_){
_start:
{
size_t v_sz_boxed_3438_; size_t v_i_boxed_3439_; lean_object* v_res_3440_; 
v_sz_boxed_3438_ = lean_unbox_usize(v_sz_3435_);
lean_dec(v_sz_3435_);
v_i_boxed_3439_ = lean_unbox_usize(v_i_3436_);
lean_dec(v_i_3436_);
v_res_3440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_boxed_3438_, v_i_boxed_3439_, v_bs_3437_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object* v_a_3441_){
_start:
{
size_t v_sz_3442_; size_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_sz_3442_ = lean_array_size(v_a_3441_);
v___x_3443_ = ((size_t)0ULL);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3442_, v___x_3443_, v_a_3441_);
v___x_3445_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t v_sz_3446_, size_t v_i_3447_, lean_object* v_bs_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v___x_3450_; 
v___x_3450_ = lean_usize_dec_lt(v_i_3447_, v_sz_3446_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v_bs_3448_);
lean_ctor_set(v___x_3451_, 1, v___y_3449_);
return v___x_3451_;
}
else
{
lean_object* v_v_3452_; lean_object* v___x_3453_; lean_object* v_fst_3454_; lean_object* v_snd_3455_; lean_object* v___x_3456_; lean_object* v_bs_x27_3457_; size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v_v_3452_ = lean_array_uget_borrowed(v_bs_3448_, v_i_3447_);
lean_inc(v_v_3452_);
v___x_3453_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3452_, v___y_3449_);
v_fst_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_fst_3454_);
v_snd_3455_ = lean_ctor_get(v___x_3453_, 1);
lean_inc(v_snd_3455_);
lean_dec_ref(v___x_3453_);
v___x_3456_ = lean_unsigned_to_nat(0u);
v_bs_x27_3457_ = lean_array_uset(v_bs_3448_, v_i_3447_, v___x_3456_);
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3447_, v___x_3458_);
v___x_3460_ = lean_array_uset(v_bs_x27_3457_, v_i_3447_, v_fst_3454_);
v_i_3447_ = v___x_3459_;
v_bs_3448_ = v___x_3460_;
v___y_3449_ = v_snd_3455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object* v_sz_3462_, lean_object* v_i_3463_, lean_object* v_bs_3464_, lean_object* v___y_3465_){
_start:
{
size_t v_sz_boxed_3466_; size_t v_i_boxed_3467_; lean_object* v_res_3468_; 
v_sz_boxed_3466_ = lean_unbox_usize(v_sz_3462_);
lean_dec(v_sz_3462_);
v_i_boxed_3467_ = lean_unbox_usize(v_i_3463_);
lean_dec(v_i_3463_);
v_res_3468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_boxed_3466_, v_i_boxed_3467_, v_bs_3464_, v___y_3465_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
size_t v_sz_3471_; size_t v___x_3472_; lean_object* v___x_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3484_; 
v_sz_3471_ = lean_array_size(v_a_3469_);
v___x_3472_ = ((size_t)0ULL);
v___x_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3471_, v___x_3472_, v_a_3469_, v_a_3470_);
v_fst_3474_ = lean_ctor_get(v___x_3473_, 0);
v_snd_3475_ = lean_ctor_get(v___x_3473_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_snd_3475_);
lean_inc(v_fst_3474_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3479_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_fst_3474_);
v___x_3480_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(v___x_3479_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3480_);
v___x_3482_ = v___x_3477_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_snd_3475_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t v_sz_3485_, size_t v_i_3486_, lean_object* v_bs_3487_){
_start:
{
uint8_t v___x_3488_; 
v___x_3488_ = lean_usize_dec_lt(v_i_3486_, v_sz_3485_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v_bs_3487_);
return v___x_3489_;
}
else
{
lean_object* v_v_3490_; lean_object* v___x_3491_; 
v_v_3490_ = lean_array_uget_borrowed(v_bs_3487_, v_i_3486_);
lean_inc(v_v_3490_);
v___x_3491_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3490_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec_ref(v_bs_3487_);
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3501_; lean_object* v_bs_x27_3502_; size_t v___x_3503_; size_t v___x_3504_; lean_object* v___x_3505_; 
v_a_3500_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3501_ = lean_unsigned_to_nat(0u);
v_bs_x27_3502_ = lean_array_uset(v_bs_3487_, v_i_3486_, v___x_3501_);
v___x_3503_ = ((size_t)1ULL);
v___x_3504_ = lean_usize_add(v_i_3486_, v___x_3503_);
v___x_3505_ = lean_array_uset(v_bs_x27_3502_, v_i_3486_, v_a_3500_);
v_i_3486_ = v___x_3504_;
v_bs_3487_ = v___x_3505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object* v_sz_3507_, lean_object* v_i_3508_, lean_object* v_bs_3509_){
_start:
{
size_t v_sz_boxed_3510_; size_t v_i_boxed_3511_; lean_object* v_res_3512_; 
v_sz_boxed_3510_ = lean_unbox_usize(v_sz_3507_);
lean_dec(v_sz_3507_);
v_i_boxed_3511_ = lean_unbox_usize(v_i_3508_);
lean_dec(v_i_3508_);
v_res_3512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_boxed_3510_, v_i_boxed_3511_, v_bs_3509_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t v_sz_3513_, size_t v_i_3514_, lean_object* v_bs_3515_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_lt(v_i_3514_, v_sz_3513_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_bs_3515_);
return v___x_3517_;
}
else
{
lean_object* v_v_3518_; lean_object* v___x_3519_; lean_object* v_bs_x27_3520_; size_t v___x_3521_; size_t v___x_3522_; lean_object* v___x_3523_; 
v_v_3518_ = lean_array_uget(v_bs_3515_, v_i_3514_);
v___x_3519_ = lean_unsigned_to_nat(0u);
v_bs_x27_3520_ = lean_array_uset(v_bs_3515_, v_i_3514_, v___x_3519_);
v___x_3521_ = ((size_t)1ULL);
v___x_3522_ = lean_usize_add(v_i_3514_, v___x_3521_);
v___x_3523_ = lean_array_uset(v_bs_x27_3520_, v_i_3514_, v_v_3518_);
v_i_3514_ = v___x_3522_;
v_bs_3515_ = v___x_3523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_sz_3525_, lean_object* v_i_3526_, lean_object* v_bs_3527_){
_start:
{
size_t v_sz_boxed_3528_; size_t v_i_boxed_3529_; lean_object* v_res_3530_; 
v_sz_boxed_3528_ = lean_unbox_usize(v_sz_3525_);
lean_dec(v_sz_3525_);
v_i_boxed_3529_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_3528_, v_i_boxed_3529_, v_bs_3527_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object* v_x_3532_){
_start:
{
if (lean_obj_tag(v_x_3532_) == 4)
{
lean_object* v_elems_3533_; size_t v_sz_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
v_elems_3533_ = lean_ctor_get(v_x_3532_, 0);
lean_inc_ref(v_elems_3533_);
lean_dec_ref_known(v_x_3532_, 1);
v_sz_3534_ = lean_array_size(v_elems_3533_);
v___x_3535_ = ((size_t)0ULL);
v___x_3536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3534_, v___x_3535_, v_elems_3533_);
return v___x_3536_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3537_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0));
v___x_3538_ = lean_unsigned_to_nat(80u);
v___x_3539_ = l_Lean_Json_pretty(v_x_3532_, v___x_3538_);
v___x_3540_ = lean_string_append(v___x_3537_, v___x_3539_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_j_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(v_j_3544_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3556_; 
v_a_3555_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3556_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_a_3555_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
else
{
lean_object* v_a_3565_; size_t v_sz_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v_a_3565_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3556_, 1);
v_sz_3566_ = lean_array_size(v_a_3565_);
v___x_3567_ = ((size_t)0ULL);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3566_, v___x_3567_, v_a_3565_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
v_a_3577_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3568_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3568_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object* v_j_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_j_3585_, v_a_3586_);
lean_dec_ref(v_a_3586_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t v_sz_3588_, size_t v_i_3589_, lean_object* v_bs_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3588_, v_i_3589_, v_bs_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object* v_sz_3593_, lean_object* v_i_3594_, lean_object* v_bs_3595_, lean_object* v___y_3596_){
_start:
{
size_t v_sz_boxed_3597_; size_t v_i_boxed_3598_; lean_object* v_res_3599_; 
v_sz_boxed_3597_ = lean_unbox_usize(v_sz_3593_);
lean_dec(v_sz_3593_);
v_i_boxed_3598_ = lean_unbox_usize(v_i_3594_);
lean_dec(v_i_3594_);
v_res_3599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_boxed_3597_, v_i_boxed_3598_, v_bs_3595_, v___y_3596_);
lean_dec_ref(v___y_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object* v_x_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
if (lean_obj_tag(v_x_3606_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3612_ = lean_ctor_get(v_x_3606_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v_x_3606_, 1);
v___x_3613_ = l_Lean_stringToMessageData(v_a_3612_);
v___x_3614_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_3613_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3614_;
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
v_a_3615_ = lean_ctor_get(v_x_3606_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_x_3606_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v_x_3606_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v_x_3606_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object* v_x_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object* v_id_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; lean_object* v_env_3637_; lean_object* v_options_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3636_ = lean_st_ref_get(v___y_3634_);
v_env_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc_ref(v_env_3637_);
lean_dec(v___x_3636_);
v_options_3638_ = lean_ctor_get(v___y_3633_, 2);
v___x_3639_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3640_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3637_, v_options_3638_, v___x_3639_, v_id_3630_);
v___x_3641_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v___x_3640_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object* v_id_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object* v___x_3649_, size_t v_sz_3650_, size_t v_i_3651_, lean_object* v_bs_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
uint8_t v___x_3658_; 
v___x_3658_ = lean_usize_dec_lt(v_i_3651_, v_sz_3650_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; 
lean_dec_ref(v___x_3649_);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_bs_3652_);
return v___x_3659_;
}
else
{
lean_object* v_v_3660_; lean_object* v_id_3661_; lean_object* v___x_3662_; lean_object* v_bs_x27_3663_; lean_object* v_a_3665_; lean_object* v___y_3675_; uint8_t v___x_3696_; lean_object* v___x_3697_; 
v_v_3660_ = lean_array_uget(v_bs_3652_, v_i_3651_);
v_id_3661_ = lean_ctor_get(v_v_3660_, 0);
v___x_3662_ = lean_unsigned_to_nat(0u);
v_bs_x27_3663_ = lean_array_uset(v_bs_3652_, v_i_3651_, v___x_3662_);
v___x_3696_ = 0;
lean_inc(v_id_3661_);
lean_inc_ref(v___x_3649_);
v___x_3697_ = l_Lean_Environment_find_x3f(v___x_3649_, v_id_3661_, v___x_3696_);
if (lean_obj_tag(v___x_3697_) == 0)
{
v___y_3675_ = v___x_3697_;
goto v___jp_3674_;
}
else
{
lean_object* v_val_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v_val_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_val_3698_);
v___x_3699_ = l_Lean_ConstantInfo_type(v_val_3698_);
lean_dec(v_val_3698_);
v___x_3700_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3701_ = l_Lean_Expr_isConstOf(v___x_3699_, v___x_3700_);
lean_dec_ref(v___x_3699_);
if (v___x_3701_ == 0)
{
lean_dec_ref_known(v___x_3697_, 1);
goto v___jp_3672_;
}
else
{
v___y_3675_ = v___x_3697_;
goto v___jp_3674_;
}
}
v___jp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; size_t v___x_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3667_, 0, v_v_3660_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
lean_ctor_set(v___x_3667_, 2, v_a_3665_);
v___x_3668_ = ((size_t)1ULL);
v___x_3669_ = lean_usize_add(v_i_3651_, v___x_3668_);
v___x_3670_ = lean_array_uset(v_bs_x27_3663_, v_i_3651_, v___x_3667_);
v_i_3651_ = v___x_3669_;
v_bs_3652_ = v___x_3670_;
goto _start;
}
v___jp_3672_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_box(0);
v_a_3665_ = v___x_3673_;
goto v___jp_3664_;
}
v___jp_3674_:
{
if (lean_obj_tag(v___y_3675_) == 0)
{
goto v___jp_3672_;
}
else
{
lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3694_; 
v_isSharedCheck_3694_ = !lean_is_exclusive(v___y_3675_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; 
v_unused_3695_ = lean_ctor_get(v___y_3675_, 0);
lean_dec(v_unused_3695_);
v___x_3677_ = v___y_3675_;
v_isShared_3678_ = v_isSharedCheck_3694_;
goto v_resetjp_3676_;
}
else
{
lean_dec(v___y_3675_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3694_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v_id_3679_; lean_object* v___x_3680_; 
v_id_3679_ = lean_ctor_get(v_v_3660_, 0);
lean_inc(v_id_3679_);
v___x_3680_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3679_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v_name_3682_; lean_object* v___x_3684_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
v_name_3682_ = lean_ctor_get(v_a_3681_, 0);
lean_inc_ref(v_name_3682_);
lean_dec(v_a_3681_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v_name_3682_);
v___x_3684_ = v___x_3677_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_name_3682_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
v_a_3665_ = v___x_3684_;
goto v___jp_3664_;
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_del_object(v___x_3677_);
lean_dec_ref(v_bs_x27_3663_);
lean_dec(v_v_3660_);
lean_dec_ref(v___x_3649_);
v_a_3686_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3680_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3680_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object* v___x_3702_, lean_object* v_sz_3703_, lean_object* v_i_3704_, lean_object* v_bs_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
size_t v_sz_boxed_3711_; size_t v_i_boxed_3712_; lean_object* v_res_3713_; 
v_sz_boxed_3711_ = lean_unbox_usize(v_sz_3703_);
lean_dec(v_sz_3703_);
v_i_boxed_3712_ = lean_unbox_usize(v_i_3704_);
lean_dec(v_i_3704_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3702_, v_sz_boxed_3711_, v_i_boxed_3712_, v_bs_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object* v___x_3714_, lean_object* v___x_3715_, size_t v_sz_3716_, size_t v_i_3717_, lean_object* v_bs_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
uint8_t v___x_3724_; 
v___x_3724_ = lean_usize_dec_lt(v_i_3717_, v_sz_3716_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; 
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v_bs_3718_);
return v___x_3725_;
}
else
{
lean_object* v_v_3726_; lean_object* v_toWidgetInstance_3727_; lean_object* v_stx_3728_; lean_object* v_id_3729_; lean_object* v___x_3730_; lean_object* v_bs_x27_3731_; lean_object* v___y_3733_; lean_object* v___y_3734_; uint8_t v___x_3740_; lean_object* v_a_3742_; lean_object* v___y_3757_; lean_object* v___x_3777_; 
v_v_3726_ = lean_array_uget_borrowed(v_bs_3718_, v_i_3717_);
v_toWidgetInstance_3727_ = lean_ctor_get(v_v_3726_, 0);
lean_inc_ref(v_toWidgetInstance_3727_);
v_stx_3728_ = lean_ctor_get(v_v_3726_, 1);
lean_inc(v_stx_3728_);
v_id_3729_ = lean_ctor_get(v_toWidgetInstance_3727_, 0);
v___x_3730_ = lean_unsigned_to_nat(0u);
v_bs_x27_3731_ = lean_array_uset(v_bs_3718_, v_i_3717_, v___x_3730_);
v___x_3740_ = 0;
lean_inc(v_id_3729_);
lean_inc_ref(v___x_3715_);
v___x_3777_ = l_Lean_Environment_find_x3f(v___x_3715_, v_id_3729_, v___x_3740_);
if (lean_obj_tag(v___x_3777_) == 0)
{
v___y_3757_ = v___x_3777_;
goto v___jp_3756_;
}
else
{
lean_object* v_val_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v_val_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_val_3778_);
v___x_3779_ = l_Lean_ConstantInfo_type(v_val_3778_);
lean_dec(v_val_3778_);
v___x_3780_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3781_ = l_Lean_Expr_isConstOf(v___x_3779_, v___x_3780_);
lean_dec_ref(v___x_3779_);
if (v___x_3781_ == 0)
{
lean_dec_ref_known(v___x_3777_, 1);
goto v___jp_3754_;
}
else
{
v___y_3757_ = v___x_3777_;
goto v___jp_3756_;
}
}
v___jp_3732_:
{
lean_object* v___x_3735_; size_t v___x_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
v___x_3735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3735_, 0, v_toWidgetInstance_3727_);
lean_ctor_set(v___x_3735_, 1, v___y_3734_);
lean_ctor_set(v___x_3735_, 2, v___y_3733_);
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3717_, v___x_3736_);
v___x_3738_ = lean_array_uset(v_bs_x27_3731_, v_i_3717_, v___x_3735_);
v_i_3717_ = v___x_3737_;
v_bs_3718_ = v___x_3738_;
goto _start;
}
v___jp_3741_:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Syntax_getRange_x3f(v_stx_3728_, v___x_3740_);
lean_dec(v_stx_3728_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_box(0);
v___y_3733_ = v_a_3742_;
v___y_3734_ = v___x_3744_;
goto v___jp_3732_;
}
else
{
lean_object* v_val_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3753_; 
v_val_3745_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3747_ = v___x_3743_;
v_isShared_3748_ = v_isSharedCheck_3753_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_val_3745_);
lean_dec(v___x_3743_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3753_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
lean_inc_ref(v___x_3714_);
v___x_3749_ = l_Lean_Syntax_Range_toLspRange(v___x_3714_, v_val_3745_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3749_);
v___x_3751_ = v___x_3747_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
v___y_3733_ = v_a_3742_;
v___y_3734_ = v___x_3751_;
goto v___jp_3732_;
}
}
}
}
v___jp_3754_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_box(0);
v_a_3742_ = v___x_3755_;
goto v___jp_3741_;
}
v___jp_3756_:
{
if (lean_obj_tag(v___y_3757_) == 0)
{
goto v___jp_3754_;
}
else
{
lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3775_; 
v_isSharedCheck_3775_ = !lean_is_exclusive(v___y_3757_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v___y_3757_, 0);
lean_dec(v_unused_3776_);
v___x_3759_ = v___y_3757_;
v_isShared_3760_ = v_isSharedCheck_3775_;
goto v_resetjp_3758_;
}
else
{
lean_dec(v___y_3757_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3775_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; 
lean_inc(v_id_3729_);
v___x_3761_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3729_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v_name_3763_; lean_object* v___x_3765_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v_name_3763_ = lean_ctor_get(v_a_3762_, 0);
lean_inc_ref(v_name_3763_);
lean_dec(v_a_3762_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_name_3763_);
v___x_3765_ = v___x_3759_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_name_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
v_a_3742_ = v___x_3765_;
goto v___jp_3741_;
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_del_object(v___x_3759_);
lean_dec_ref(v_bs_x27_3731_);
lean_dec(v_stx_3728_);
lean_dec_ref(v_toWidgetInstance_3727_);
lean_dec_ref(v___x_3715_);
lean_dec_ref(v___x_3714_);
v_a_3767_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3761_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3761_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object* v___x_3782_, lean_object* v___x_3783_, lean_object* v_sz_3784_, lean_object* v_i_3785_, lean_object* v_bs_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
size_t v_sz_boxed_3792_; size_t v_i_boxed_3793_; lean_object* v_res_3794_; 
v_sz_boxed_3792_ = lean_unbox_usize(v_sz_3784_);
lean_dec(v_sz_3784_);
v_i_boxed_3793_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3782_, v___x_3783_, v_sz_boxed_3792_, v_i_boxed_3793_, v_bs_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object* v_pos_3795_, lean_object* v_text_3796_, lean_object* v_val_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_st_ref_get(v___y_3801_);
v___x_3804_ = l_Lean_Widget_evalPanelWidgets(v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v_env_3806_; size_t v_sz_3807_; size_t v___x_3808_; lean_object* v___x_3809_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v_env_3806_ = lean_ctor_get(v___x_3803_, 0);
lean_inc_ref_n(v_env_3806_, 2);
lean_dec(v___x_3803_);
v_sz_3807_ = lean_array_size(v_a_3805_);
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v_env_3806_, v_sz_3807_, v___x_3808_, v_a_3805_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v_line_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; size_t v_sz_3814_; lean_object* v___x_3815_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v_line_3811_ = lean_ctor_get(v_pos_3795_, 0);
lean_inc(v_line_3811_);
lean_dec_ref(v_pos_3795_);
lean_inc_ref(v_text_3796_);
v___x_3812_ = l_Lean_Widget_widgetInfosAt_x3f(v_text_3796_, v_val_3797_, v_line_3811_);
v___x_3813_ = lean_array_mk(v___x_3812_);
v_sz_3814_ = lean_array_size(v___x_3813_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v_text_3796_, v_env_3806_, v_sz_3814_, v___x_3808_, v___x_3813_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3824_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = l_Array_append___redArg(v_a_3810_, v_a_3816_);
lean_dec(v_a_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec(v_a_3810_);
v_a_3825_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3815_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3815_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v_env_3806_);
lean_dec_ref(v_val_3797_);
lean_dec_ref(v_text_3796_);
lean_dec_ref(v_pos_3795_);
v_a_3833_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3809_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3809_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec(v___x_3803_);
lean_dec_ref(v_val_3797_);
lean_dec_ref(v_text_3796_);
lean_dec_ref(v_pos_3795_);
v_a_3841_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3804_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3804_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object* v_pos_3849_, lean_object* v_text_3850_, lean_object* v_val_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3849_, v_text_3850_, v_val_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object* v_pos_3862_, lean_object* v_text_3863_, lean_object* v_x_3864_, lean_object* v___y_3865_){
_start:
{
if (lean_obj_tag(v_x_3864_) == 1)
{
lean_object* v_val_3870_; 
v_val_3870_ = lean_ctor_get(v_x_3864_, 0);
lean_inc(v_val_3870_);
lean_dec_ref_known(v_x_3864_, 1);
if (lean_obj_tag(v_val_3870_) == 0)
{
lean_object* v_i_3871_; 
v_i_3871_ = lean_ctor_get(v_val_3870_, 0);
if (lean_obj_tag(v_i_3871_) == 0)
{
lean_object* v_info_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_info_3872_ = lean_ctor_get(v_i_3871_, 0);
lean_inc_ref(v_info_3872_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3873_, 0, v_pos_3862_);
lean_closure_set(v___f_3873_, 1, v_text_3863_);
lean_closure_set(v___f_3873_, 2, v_val_3870_);
v___x_3874_ = lean_box(0);
v___x_3875_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__1));
v___x_3876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3876_, 0, v_info_3872_);
lean_ctor_set(v___x_3876_, 1, v___x_3874_);
lean_ctor_set(v___x_3876_, 2, v___x_3875_);
v___x_3877_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_3878_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_3876_, v___x_3877_, v___f_3873_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3895_; 
v_a_3887_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3889_ = v___x_3878_;
v_isShared_3890_ = v_isSharedCheck_3895_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3878_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3895_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3893_; 
v___x_3891_ = l_Lean_Server_RequestError_ofIoError(v_a_3887_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3891_);
v___x_3893_ = v___x_3889_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_dec_ref_known(v_val_3870_, 2);
lean_dec_ref(v_text_3863_);
lean_dec_ref(v_pos_3862_);
goto v___jp_3867_;
}
}
else
{
lean_dec(v_val_3870_);
lean_dec_ref(v_text_3863_);
lean_dec_ref(v_pos_3862_);
goto v___jp_3867_;
}
}
else
{
lean_dec(v_x_3864_);
lean_dec_ref(v_text_3863_);
lean_dec_ref(v_pos_3862_);
goto v___jp_3867_;
}
v___jp_3867_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__0));
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
return v___x_3869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object* v_pos_3896_, lean_object* v_text_3897_, lean_object* v_x_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3896_, v_text_3897_, v_x_3898_, v___y_3899_);
lean_dec_ref(v___y_3899_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets(lean_object* v_pos_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v___x_3905_; lean_object* v_a_3906_; lean_object* v_toEditableDocumentCore_3907_; lean_object* v_meta_3908_; lean_object* v_text_3909_; lean_object* v___f_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3905_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_3903_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___x_3905_);
v_toEditableDocumentCore_3907_ = lean_ctor_get(v_a_3906_, 0);
v_meta_3908_ = lean_ctor_get(v_toEditableDocumentCore_3907_, 0);
v_text_3909_ = lean_ctor_get(v_meta_3908_, 3);
lean_inc_ref(v_text_3909_);
lean_inc_ref(v_pos_3902_);
v___f_3910_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3910_, 0, v_pos_3902_);
lean_closure_set(v___f_3910_, 1, v_text_3909_);
v___x_3911_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3909_, v_pos_3902_);
v___x_3912_ = 1;
v___x_3913_ = l_Lean_Server_RequestM_findInfoTreeAtPos(v_a_3906_, v___x_3911_, v___x_3912_);
v___x_3914_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3913_, v___f_3910_, v_a_3903_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object* v_pos_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_Widget_getWidgets(v_pos_3915_, v_a_3916_);
lean_dec_ref(v_a_3916_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object* v_00_u03b1_3919_, lean_object* v_x_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3927_, lean_object* v_x_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(v_00_u03b1_3927_, v_x_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object* v_val_3935_, lean_object* v___f_3936_, lean_object* v_x_3937_, lean_object* v___y_3938_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec_ref(v___f_3936_);
v_a_3940_ = lean_ctor_get(v_x_3937_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_x_3937_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v_x_3937_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v_x_3937_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
lean_ctor_set_tag(v___x_3942_, 1);
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3964_; 
v_a_3948_ = lean_ctor_get(v_x_3937_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_x_3937_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3950_ = v_x_3937_;
v_isShared_3951_ = v_isSharedCheck_3964_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v_x_3937_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3964_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3952_; lean_object* v_objects_3953_; lean_object* v_expireTime_3954_; lean_object* v___f_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v_fst_3958_; lean_object* v_snd_3959_; lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3952_ = lean_st_ref_take(v_val_3935_);
v_objects_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc_ref(v_objects_3953_);
v_expireTime_3954_ = lean_ctor_get(v___x_3952_, 1);
lean_inc(v_expireTime_3954_);
lean_dec(v___x_3952_);
v___f_3955_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_3955_, 0, v_expireTime_3954_);
v___x_3956_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_a_3948_, v_objects_3953_);
v___x_3957_ = l_Prod_map___redArg(v___f_3936_, v___f_3955_, v___x_3956_);
v_fst_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_fst_3958_);
v_snd_3959_ = lean_ctor_get(v___x_3957_, 1);
lean_inc(v_snd_3959_);
lean_dec_ref(v___x_3957_);
v___x_3960_ = lean_st_ref_set(v_val_3935_, v_snd_3959_);
if (v_isShared_3951_ == 0)
{
lean_ctor_set_tag(v___x_3950_, 0);
lean_ctor_set(v___x_3950_, 0, v_fst_3958_);
v___x_3962_ = v___x_3950_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_fst_3958_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object* v_val_3965_, lean_object* v___f_3966_, lean_object* v_x_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_3965_, v___f_3966_, v_x_3967_, v___y_3968_);
lean_dec_ref(v___y_3968_);
lean_dec(v_val_3965_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object* v_method_3971_, lean_object* v_handler_3972_, lean_object* v___f_3973_, uint64_t v_seshId_3974_, lean_object* v_j_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_rpcSessions_3978_; lean_object* v___x_3979_; 
v_rpcSessions_3978_ = lean_ctor_get(v___y_3976_, 0);
v___x_3979_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_3978_, v_seshId_3974_);
if (lean_obj_tag(v___x_3979_) == 1)
{
lean_object* v_val_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_val_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = lean_st_ref_get(v_val_3980_);
lean_dec(v___x_3981_);
lean_inc(v_j_3975_);
v___x_3982_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v_j_3975_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v_val_3980_);
lean_dec_ref(v___f_3973_);
lean_dec_ref(v_handler_3972_);
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3985_ = v___x_3982_;
v_isShared_3986_ = v_isSharedCheck_4003_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4003_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
uint8_t v___x_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3987_ = 3;
v___x_3988_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_3989_ = 1;
v___x_3990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_3971_, v___x_3989_);
v___x_3991_ = lean_string_append(v___x_3988_, v___x_3990_);
lean_dec_ref(v___x_3990_);
v___x_3992_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_3993_ = lean_string_append(v___x_3991_, v___x_3992_);
v___x_3994_ = l_Lean_Json_compress(v_j_3975_);
v___x_3995_ = lean_string_append(v___x_3993_, v___x_3994_);
lean_dec_ref(v___x_3994_);
v___x_3996_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_3997_ = lean_string_append(v___x_3995_, v___x_3996_);
v___x_3998_ = lean_string_append(v___x_3997_, v_a_3983_);
lean_dec(v_a_3983_);
v___x_3999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
lean_ctor_set_uint8(v___x_3999_, sizeof(void*)*1, v___x_3987_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set_tag(v___x_3985_, 1);
lean_ctor_set(v___x_3985_, 0, v___x_3999_);
v___x_4001_ = v___x_3985_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4005_; 
lean_dec(v_j_3975_);
lean_dec(v_method_3971_);
v_a_4004_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_3982_, 1);
lean_inc_ref(v___y_3976_);
v___x_4005_ = lean_apply_3(v_handler_3972_, v_a_4004_, v___y_3976_, lean_box(0));
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___f_4007_; lean_object* v___x_4008_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v___f_4007_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4007_, 0, v_val_3980_);
lean_closure_set(v___f_4007_, 1, v___f_3973_);
v___x_4008_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_4006_, v___f_4007_, v___y_3976_);
return v___x_4008_;
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_val_3980_);
lean_dec_ref(v___f_3973_);
v_a_4009_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4005_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4005_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec(v___x_3979_);
lean_dec(v_j_3975_);
lean_dec_ref(v___f_3973_);
lean_dec_ref(v_handler_3972_);
lean_dec(v_method_3971_);
v___x_4017_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_method_4019_, lean_object* v_handler_4020_, lean_object* v___f_4021_, lean_object* v_seshId_4022_, lean_object* v_j_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
uint64_t v_seshId_boxed_4026_; lean_object* v_res_4027_; 
v_seshId_boxed_4026_ = lean_unbox_uint64(v_seshId_4022_);
lean_dec_ref(v_seshId_4022_);
v_res_4027_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_method_4019_, v_handler_4020_, v___f_4021_, v_seshId_boxed_4026_, v_j_4023_, v___y_4024_);
lean_dec_ref(v___y_4024_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_4028_, lean_object* v_handler_4029_){
_start:
{
lean_object* v___f_4030_; lean_object* v___f_4031_; 
v___f_4030_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_4031_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4031_, 0, v_method_4028_);
lean_closure_set(v___f_4031_, 1, v_handler_4029_);
lean_closure_set(v___f_4031_, 2, v___f_4030_);
return v___f_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object* v_method_4032_, lean_object* v_handler_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4069_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4069_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4069_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; uint8_t v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v_errMsg_4045_; uint8_t v___x_4046_; 
v___x_4040_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_4041_ = 1;
lean_inc(v_method_4032_);
v___x_4042_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_4032_, v___x_4041_);
v___x_4043_ = lean_string_append(v___x_4040_, v___x_4042_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_4045_ = lean_string_append(v___x_4043_, v___x_4044_);
v___x_4046_ = lean_unbox(v_a_4036_);
lean_dec(v_a_4036_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4051_; 
lean_dec_ref(v_handler_4033_);
lean_dec(v_method_4032_);
v___x_4047_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_4048_ = lean_string_append(v_errMsg_4045_, v___x_4047_);
v___x_4049_ = lean_mk_io_user_error(v___x_4048_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 1);
lean_ctor_set(v___x_4038_, 0, v___x_4049_);
v___x_4051_ = v___x_4038_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4053_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_4054_ = lean_st_ref_get(v___x_4053_);
v___x_4055_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4054_, v_method_4032_);
lean_dec(v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_dec_ref(v_errMsg_4045_);
v___x_4056_ = lean_st_ref_take(v___x_4053_);
lean_inc(v_method_4032_);
v___x_4057_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(v_method_4032_, v_handler_4033_);
v___x_4058_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4056_, v_method_4032_, v___x_4057_);
v___x_4059_ = lean_st_ref_set(v___x_4053_, v___x_4058_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4059_);
v___x_4061_ = v___x_4038_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4067_; 
lean_dec_ref(v_handler_4033_);
lean_dec(v_method_4032_);
v___x_4063_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_4064_ = lean_string_append(v_errMsg_4045_, v___x_4063_);
v___x_4065_ = lean_mk_io_user_error(v___x_4064_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 1);
lean_ctor_set(v___x_4038_, 0, v___x_4065_);
v___x_4067_ = v___x_4038_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_handler_4033_);
lean_dec(v_method_4032_);
v_a_4070_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4035_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4035_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4078_, lean_object* v_handler_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_4078_, v_handler_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4090_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4091_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v___x_4089_, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
return v_res_4093_;
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
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
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
