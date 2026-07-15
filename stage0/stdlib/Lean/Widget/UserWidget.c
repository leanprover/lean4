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
uint8_t l_Lean_initializing();
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
uint8_t v___y_10918__boxed_804_; uint8_t v_suppressElabErrors_boxed_805_; uint8_t v_res_806_; lean_object* v_r_807_; 
v___y_10918__boxed_804_ = lean_unbox(v___y_801_);
v_suppressElabErrors_boxed_805_ = lean_unbox(v_suppressElabErrors_802_);
v_res_806_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v___y_10918__boxed_804_, v_suppressElabErrors_boxed_805_, v_x_803_);
lean_dec(v_x_803_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_ref_809_, lean_object* v_msgData_810_, uint8_t v_severity_811_, uint8_t v_isSilent_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; uint8_t v___y_822_; uint8_t v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_855_; lean_object* v___y_856_; uint8_t v___y_857_; uint8_t v___y_858_; lean_object* v___y_859_; uint8_t v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_880_; lean_object* v___y_881_; uint8_t v___y_882_; uint8_t v___y_883_; lean_object* v___y_884_; uint8_t v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_891_; lean_object* v___y_892_; uint8_t v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; uint8_t v___x_902_; lean_object* v___y_904_; lean_object* v___y_905_; uint8_t v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; uint8_t v___y_909_; uint8_t v___y_910_; uint8_t v___y_912_; uint8_t v___x_927_; 
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
lean_ctor_set(v___x_844_, 1, v___y_825_);
lean_inc_ref(v___y_821_);
lean_inc_ref(v___y_824_);
v___x_845_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_845_, 0, v___y_824_);
lean_ctor_set(v___x_845_, 1, v___y_820_);
lean_ctor_set(v___x_845_, 2, v___y_819_);
lean_ctor_set(v___x_845_, 3, v___y_821_);
lean_ctor_set(v___x_845_, 4, v___x_844_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*5, v___y_823_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*5 + 1, v___y_822_);
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
lean_inc_ref_n(v___y_856_, 2);
v___x_869_ = l_Lean_FileMap_toPosition(v___y_856_, v___y_861_);
lean_dec(v___y_861_);
v___x_870_ = l_Lean_FileMap_toPosition(v___y_856_, v___y_862_);
lean_dec(v___y_862_);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
if (v___y_858_ == 0)
{
lean_del_object(v___x_867_);
lean_dec_ref(v___y_855_);
v___y_819_ = v___x_871_;
v___y_820_ = v___x_869_;
v___y_821_ = v___x_872_;
v___y_822_ = v___y_857_;
v___y_823_ = v___y_860_;
v___y_824_ = v___y_859_;
v___y_825_ = v_a_865_;
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
v___y_819_ = v___x_871_;
v___y_820_ = v___x_869_;
v___y_821_ = v___x_872_;
v___y_822_ = v___y_857_;
v___y_823_ = v___y_860_;
v___y_824_ = v___y_859_;
v___y_825_ = v_a_865_;
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
v___x_888_ = l_Lean_Syntax_getTailPos_x3f(v___y_884_, v___y_885_);
lean_dec(v___y_884_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_inc(v___y_887_);
v___y_855_ = v___y_880_;
v___y_856_ = v___y_881_;
v___y_857_ = v___y_882_;
v___y_858_ = v___y_883_;
v___y_859_ = v___y_886_;
v___y_860_ = v___y_885_;
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
v___y_857_ = v___y_882_;
v___y_858_ = v___y_883_;
v___y_859_ = v___y_886_;
v___y_860_ = v___y_885_;
v___y_861_ = v___y_887_;
v___y_862_ = v_val_889_;
goto v___jp_854_;
}
}
v___jp_890_:
{
lean_object* v_ref_898_; lean_object* v___x_899_; 
v_ref_898_ = l_Lean_replaceRef(v_ref_809_, v___y_896_);
v___x_899_ = l_Lean_Syntax_getPos_x3f(v_ref_898_, v___y_895_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___y_880_ = v___y_891_;
v___y_881_ = v___y_892_;
v___y_882_ = v___y_897_;
v___y_883_ = v___y_893_;
v___y_884_ = v_ref_898_;
v___y_885_ = v___y_895_;
v___y_886_ = v___y_894_;
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
v___y_882_ = v___y_897_;
v___y_883_ = v___y_893_;
v___y_884_ = v_ref_898_;
v___y_885_ = v___y_895_;
v___y_886_ = v___y_894_;
v___y_887_ = v_val_901_;
goto v___jp_879_;
}
}
v___jp_903_:
{
if (v___y_910_ == 0)
{
v___y_891_ = v___y_904_;
v___y_892_ = v___y_905_;
v___y_893_ = v___y_906_;
v___y_894_ = v___y_908_;
v___y_895_ = v___y_909_;
v___y_896_ = v___y_907_;
v___y_897_ = v_severity_811_;
goto v___jp_890_;
}
else
{
v___y_891_ = v___y_904_;
v___y_892_ = v___y_905_;
v___y_893_ = v___y_906_;
v___y_894_ = v___y_908_;
v___y_895_ = v___y_909_;
v___y_896_ = v___y_907_;
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
v___y_905_ = v_fileMap_914_;
v___y_906_ = v_suppressElabErrors_917_;
v___y_907_ = v_ref_916_;
v___y_908_ = v_fileName_913_;
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
v___y_905_ = v_fileMap_914_;
v___y_906_ = v_suppressElabErrors_917_;
v___y_907_ = v_ref_916_;
v___y_908_ = v_fileName_913_;
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
lean_dec(v___y_1023_);
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
lean_ctor_set(v___x_1035_, 1, v___y_1022_);
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
lean_dec_ref(v___y_1022_);
lean_inc(v___y_1023_);
lean_inc_n(v_decl_1010_, 2);
v___x_1041_ = l_Lean_mkConst(v_decl_1010_, v___y_1023_);
v___x_1042_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1043_ = l_Lean_Name_mkStr3(v___x_1011_, v___x_1012_, v___x_1042_);
v___x_1044_ = l_Lean_mkConst(v___x_1043_, v___y_1023_);
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
v_javascriptHash_1060_ = lean_ctor_get_uint64(v___y_1052_, sizeof(void*)*1);
v___x_1061_ = lean_box(1);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1061_, v___x_1057_, v___y_1050_, v_asyncMode_1059_, v___x_1062_);
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
v___y_1023_ = v___y_1051_;
v___y_1024_ = v___y_1052_;
v___y_1025_ = v___y_1053_;
v___y_1026_ = v___y_1054_;
v___y_1027_ = v___y_1055_;
v___y_1028_ = v___y_1056_;
goto v___jp_1021_;
}
else
{
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
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
v___y_1023_ = v___y_1051_;
v___y_1024_ = v___y_1052_;
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
v___y_1049_ = v_a_1094_;
v___y_1050_ = v_env_1098_;
v___y_1051_ = v___x_1088_;
v___y_1052_ = v_a_1096_;
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
v___y_1049_ = v_a_1094_;
v___y_1050_ = v_env_1098_;
v___y_1051_ = v___x_1088_;
v___y_1052_ = v_a_1096_;
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
v___y_1049_ = v_a_1094_;
v___y_1050_ = v_env_1105_;
v___y_1051_ = v___x_1088_;
v___y_1052_ = v_a_1096_;
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
uint8_t v_builtin_boxed_1139_; uint8_t v___x_11286__boxed_1140_; uint8_t v_kind_boxed_1141_; lean_object* v_res_1142_; 
v_builtin_boxed_1139_ = lean_unbox(v_builtin_1127_);
v___x_11286__boxed_1140_ = lean_unbox(v___x_1131_);
v_kind_boxed_1141_ = lean_unbox(v_kind_1132_);
v_res_1142_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v_stx_1126_, v_builtin_boxed_1139_, v_decl_1128_, v___x_1129_, v___x_1130_, v___x_11286__boxed_1140_, v_kind_boxed_1141_, v_name_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
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
lean_object* v___x_1201_; lean_object* v_env_1202_; uint8_t v_isExporting_1203_; lean_object* v___x_1269_; uint8_t v_isModule_1270_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v_isExporting_1203_ = lean_ctor_get_uint8(v_env_1202_, sizeof(void*)*8);
v___x_1269_ = l_Lean_Environment_header(v_env_1202_);
lean_dec_ref(v_env_1202_);
v_isModule_1270_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1269_);
if (v_isModule_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v___x_1271_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1271_;
}
else
{
if (v_isExporting_1203_ == 0)
{
if (v_isExporting_1195_ == 0)
{
lean_object* v___x_1272_; 
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v___x_1272_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1272_;
}
else
{
goto v___jp_1204_;
}
}
else
{
if (v_isExporting_1195_ == 0)
{
goto v___jp_1204_;
}
else
{
lean_object* v___x_1273_; 
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v___x_1273_ = lean_apply_5(v_x_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1273_;
}
}
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
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object* v_x_1274_, lean_object* v_isExporting_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v_isExporting_boxed_1281_; lean_object* v_res_1282_; 
v_isExporting_boxed_1281_ = lean_unbox(v_isExporting_1275_);
v_res_1282_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1274_, v_isExporting_boxed_1281_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(lean_object* v_x_1283_, uint8_t v_when_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
if (v_when_1284_ == 0)
{
lean_object* v___x_1290_; 
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
v___x_1290_ = lean_apply_5(v_x_1283_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, lean_box(0));
return v___x_1290_;
}
else
{
uint8_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = 0;
v___x_1292_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1283_, v___x_1291_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_x_1293_, lean_object* v_when_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_when_boxed_1300_; lean_object* v_res_1301_; 
v_when_boxed_1300_ = lean_unbox(v_when_1294_);
v_res_1301_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v_x_1293_, v_when_boxed_1300_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1301_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = lean_box(1);
v___x_1306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1307_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1306_);
lean_ctor_set(v___x_1308_, 2, v___x_1305_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
lean_ctor_set(v___x_1313_, 3, v___x_1312_);
lean_ctor_set(v___x_1313_, 4, v___x_1311_);
lean_ctor_set(v___x_1313_, 5, v___x_1311_);
lean_ctor_set(v___x_1313_, 6, v___x_1311_);
lean_ctor_set(v___x_1313_, 7, v___x_1311_);
lean_ctor_set(v___x_1313_, 8, v___x_1311_);
lean_ctor_set(v___x_1313_, 9, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1315_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set(v___x_1315_, 2, v___x_1314_);
lean_ctor_set(v___x_1315_, 3, v___x_1314_);
lean_ctor_set(v___x_1315_, 4, v___x_1314_);
lean_ctor_set(v___x_1315_, 5, v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
lean_ctor_set(v___x_1317_, 2, v___x_1316_);
lean_ctor_set(v___x_1317_, 3, v___x_1316_);
lean_ctor_set(v___x_1317_, 4, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(uint8_t v___x_1318_, lean_object* v___x_1319_, uint8_t v_builtin_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_name_1323_, lean_object* v_decl_1324_, lean_object* v_stx_1325_, uint8_t v_kind_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v___x_1330_; uint8_t v___x_1331_; uint8_t v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; uint64_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v___x_1330_ = 0;
v___x_1331_ = 1;
v___x_1332_ = 0;
v___x_1333_ = 2;
v___x_1334_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1334_, 0, v___x_1330_);
lean_ctor_set_uint8(v___x_1334_, 1, v___x_1330_);
lean_ctor_set_uint8(v___x_1334_, 2, v___x_1330_);
lean_ctor_set_uint8(v___x_1334_, 3, v___x_1330_);
lean_ctor_set_uint8(v___x_1334_, 4, v___x_1330_);
lean_ctor_set_uint8(v___x_1334_, 5, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 6, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 7, v___x_1330_);
lean_ctor_set_uint8(v___x_1334_, 8, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 9, v___x_1331_);
lean_ctor_set_uint8(v___x_1334_, 10, v___x_1332_);
lean_ctor_set_uint8(v___x_1334_, 11, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 12, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 13, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 14, v___x_1333_);
lean_ctor_set_uint8(v___x_1334_, 15, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 16, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 17, v___x_1318_);
lean_ctor_set_uint8(v___x_1334_, 18, v___x_1318_);
v___x_1335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set_uint64(v___x_1336_, sizeof(void*)*1, v___x_1335_);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1339_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1340_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1341_ = lean_box(0);
lean_inc(v___x_1319_);
v___x_1342_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1342_, 0, v___x_1336_);
lean_ctor_set(v___x_1342_, 1, v___x_1319_);
lean_ctor_set(v___x_1342_, 2, v___x_1339_);
lean_ctor_set(v___x_1342_, 3, v___x_1340_);
lean_ctor_set(v___x_1342_, 4, v___x_1341_);
lean_ctor_set(v___x_1342_, 5, v___x_1337_);
lean_ctor_set(v___x_1342_, 6, v___x_1341_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7, v___x_1330_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7 + 1, v___x_1330_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7 + 2, v___x_1330_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*7 + 3, v___x_1318_);
v___x_1343_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1344_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1345_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
lean_ctor_set(v___x_1346_, 2, v___x_1319_);
lean_ctor_set(v___x_1346_, 3, v___x_1338_);
lean_ctor_set(v___x_1346_, 4, v___x_1345_);
v___x_1347_ = lean_st_mk_ref(v___x_1346_);
v___x_1348_ = lean_box(v_builtin_1320_);
v___x_1349_ = lean_box(v___x_1318_);
v___x_1350_ = lean_box(v_kind_1326_);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 13, 8);
lean_closure_set(v___f_1351_, 0, v_stx_1325_);
lean_closure_set(v___f_1351_, 1, v___x_1348_);
lean_closure_set(v___f_1351_, 2, v_decl_1324_);
lean_closure_set(v___f_1351_, 3, v___x_1321_);
lean_closure_set(v___f_1351_, 4, v___x_1322_);
lean_closure_set(v___f_1351_, 5, v___x_1349_);
lean_closure_set(v___f_1351_, 6, v___x_1350_);
lean_closure_set(v___f_1351_, 7, v_name_1323_);
v___x_1352_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v___f_1351_, v___x_1318_, v___x_1342_, v___x_1347_, v___y_1327_, v___y_1328_);
lean_dec_ref_known(v___x_1342_, 7);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_st_ref_get(v___x_1347_);
lean_dec(v___x_1347_);
lean_dec(v___x_1357_);
if (v_isShared_1356_ == 0)
{
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1353_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_dec(v___x_1347_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v_builtin_1364_, lean_object* v___x_1365_, lean_object* v___x_1366_, lean_object* v_name_1367_, lean_object* v_decl_1368_, lean_object* v_stx_1369_, lean_object* v_kind_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v___x_11826__boxed_1374_; uint8_t v_builtin_boxed_1375_; uint8_t v_kind_boxed_1376_; lean_object* v_res_1377_; 
v___x_11826__boxed_1374_ = lean_unbox(v___x_1362_);
v_builtin_boxed_1375_ = lean_unbox(v_builtin_1364_);
v_kind_boxed_1376_ = lean_unbox(v_kind_1370_);
v_res_1377_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_11826__boxed_1374_, v___x_1363_, v_builtin_boxed_1375_, v___x_1365_, v___x_1366_, v_name_1367_, v_decl_1368_, v_stx_1369_, v_kind_boxed_1376_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(lean_object* v___x_1385_, uint8_t v_builtin_1386_, lean_object* v_name_1387_){
_start:
{
lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; lean_object* v___y_1398_; 
lean_inc_n(v_name_1387_, 2);
v___f_1389_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1389_, 0, v_name_1387_);
v___x_1390_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0));
v___x_1391_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1));
v___x_1392_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1393_ = 1;
v___x_1394_ = lean_box(v___x_1393_);
v___x_1395_ = lean_box(v_builtin_1386_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1396_, 0, v___x_1394_);
lean_closure_set(v___f_1396_, 1, v___x_1385_);
lean_closure_set(v___f_1396_, 2, v___x_1395_);
lean_closure_set(v___f_1396_, 3, v___x_1390_);
lean_closure_set(v___f_1396_, 4, v___x_1391_);
lean_closure_set(v___f_1396_, 5, v_name_1387_);
if (v_builtin_1386_ == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___y_1398_ = v___x_1421_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___y_1398_ = v___x_1422_;
goto v___jp_1397_;
}
v___jp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v_impl_1403_; lean_object* v___x_1404_; 
v___x_1399_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
lean_inc_ref(v___y_1398_);
v___x_1400_ = lean_string_append(v___y_1398_, v___x_1399_);
v___x_1401_ = 1;
v___x_1402_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1402_, 0, v___x_1392_);
lean_ctor_set(v___x_1402_, 1, v_name_1387_);
lean_ctor_set(v___x_1402_, 2, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3, v___x_1401_);
v_impl_1403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_impl_1403_, 0, v___x_1402_);
lean_ctor_set(v_impl_1403_, 1, v___f_1396_);
lean_ctor_set(v_impl_1403_, 2, v___f_1389_);
lean_inc_ref(v_impl_1403_);
v___x_1404_ = l_Lean_registerBuiltinAttribute(v_impl_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1404_, 0);
lean_dec(v_unused_1412_);
v___x_1406_ = v___x_1404_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v___x_1404_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_impl_1403_);
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_impl_1403_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref_known(v_impl_1403_, 3);
v_a_1413_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1404_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1404_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v___x_1423_, lean_object* v_builtin_1424_, lean_object* v_name_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_builtin_boxed_1427_; lean_object* v_res_1428_; 
v_builtin_boxed_1427_ = lean_unbox(v_builtin_1424_);
v_res_1428_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1423_, v_builtin_boxed_1427_, v_name_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_box(1);
v___x_1437_ = 1;
v___x_1438_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1439_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1436_, v___x_1437_, v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref_known(v___x_1439_, 1);
v___x_1440_ = 0;
v___x_1441_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1442_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_(v___x_1436_, v___x_1440_, v___x_1441_);
return v___x_1442_;
}
else
{
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2____boxed(lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_();
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v_msg_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0(v_00_u03b1_1451_, v_msg_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_1457_, lean_object* v_t_1458_, uint64_t v_k_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_t_1458_, v_k_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_1461_, lean_object* v_t_1462_, lean_object* v_k_1463_){
_start:
{
uint64_t v_k_boxed_1464_; lean_object* v_res_1465_; 
v_k_boxed_1464_ = lean_unbox_uint64(v_k_1463_);
lean_dec_ref(v_k_1463_);
v_res_1465_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2(v_00_u03b4_1461_, v_t_1462_, v_k_boxed_1464_);
lean_dec(v_t_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1466_, lean_object* v_name_1467_, uint8_t v_kind_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___redArg(v_name_1467_, v_kind_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1475_, lean_object* v_name_1476_, lean_object* v_kind_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_kind_boxed_1483_; lean_object* v_res_1484_; 
v_kind_boxed_1483_ = lean_unbox(v_kind_1477_);
v_res_1484_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4(v_00_u03b1_1475_, v_name_1476_, v_kind_boxed_1483_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(lean_object* v_00_u03b1_1485_, lean_object* v_x_1486_, uint8_t v_isExporting_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1486_, v_isExporting_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_x_1495_, lean_object* v_isExporting_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_isExporting_boxed_1502_; lean_object* v_res_1503_; 
v_isExporting_boxed_1502_ = lean_unbox(v_isExporting_1496_);
v_res_1503_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5_spec__8(v_00_u03b1_1494_, v_x_1495_, v_isExporting_boxed_1502_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1504_, lean_object* v_x_1505_, uint8_t v_when_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___redArg(v_x_1505_, v_when_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_x_1514_, lean_object* v_when_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_when_boxed_1521_; lean_object* v_res_1522_; 
v_when_boxed_1521_ = lean_unbox(v_when_1515_);
v_res_1522_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__5(v_00_u03b1_1513_, v_x_1514_, v_when_boxed_1521_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_msg_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1531_, v_msg_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
if (lean_obj_tag(v_a_1539_) == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_array_to_list(v_a_1540_);
return v___x_1541_;
}
else
{
lean_object* v_head_1542_; lean_object* v_tail_1543_; lean_object* v___x_1544_; 
v_head_1542_ = lean_ctor_get(v_a_1539_, 0);
lean_inc(v_head_1542_);
v_tail_1543_ = lean_ctor_get(v_a_1539_, 1);
lean_inc(v_tail_1543_);
lean_dec_ref_known(v_a_1539_, 2);
v___x_1544_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1540_, v_head_1542_);
v_a_1539_ = v_tail_1543_;
v_a_1540_ = v___x_1544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object* v_x_1550_){
_start:
{
uint64_t v_hash_1551_; lean_object* v_pos_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_hash_1551_ = lean_ctor_get_uint64(v_x_1550_, sizeof(void*)*1);
v_pos_1552_ = lean_ctor_get(v_x_1550_, 0);
lean_inc_ref(v_pos_1552_);
lean_dec_ref(v_x_1550_);
v___x_1553_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
v___x_1554_ = lean_uint64_to_nat(v_hash_1551_);
v___x_1555_ = l_Lean_bignumToJson(v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1553_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1560_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_1552_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1557_);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v___x_1557_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1558_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1566_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1564_, v___x_1565_);
v___x_1567_ = l_Lean_Json_mkObj(v___x_1566_);
lean_dec(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object* v_j_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = l_Lean_Json_getObjValD(v_j_1570_, v_k_1571_);
v___x_1573_ = l_Lean_UInt64_fromJson_x3f(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object* v_j_1574_, lean_object* v_k_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_j_1574_, v_k_1575_);
lean_dec_ref(v_k_1575_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object* v_j_1577_, lean_object* v_k_1578_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = l_Lean_Json_getObjValD(v_j_1577_, v_k_1578_);
v___x_1580_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object* v_j_1581_, lean_object* v_k_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_j_1581_, v_k_1582_);
lean_dec_ref(v_k_1582_);
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = 1;
v___x_1590_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1));
v___x_1591_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1593_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2);
v___x_1594_ = lean_string_append(v___x_1593_, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = 1;
v___x_1598_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4));
v___x_1599_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5);
v___x_1601_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1602_ = lean_string_append(v___x_1601_, v___x_1600_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1605_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6);
v___x_1606_ = lean_string_append(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = 1;
v___x_1610_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9));
v___x_1611_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1610_, v___x_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10);
v___x_1613_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1614_ = lean_string_append(v___x_1613_, v___x_1612_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1616_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11);
v___x_1617_ = lean_string_append(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object* v_json_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
lean_inc(v_json_1618_);
v___x_1620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_json_1618_, v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_json_1618_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8);
v___x_1626_ = lean_string_append(v___x_1625_, v_a_1621_);
lean_dec(v_a_1621_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_json_1618_);
v_a_1631_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1620_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1620_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 0);
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1639_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1640_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1641_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_json_1618_, v___x_1640_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1639_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1646_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12);
v___x_1647_ = lean_string_append(v___x_1646_, v_a_1642_);
lean_dec(v_a_1642_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1647_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_a_1639_);
v_a_1652_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1641_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1641_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set_tag(v___x_1654_, 0);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1669_; 
v_a_1660_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1662_ = v___x_1641_;
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1641_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; uint64_t v___x_1665_; lean_object* v___x_1667_; 
v___x_1664_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1664_, 0, v_a_1660_);
v___x_1665_ = lean_unbox_uint64(v_a_1639_);
lean_dec(v_a_1639_);
lean_ctor_set_uint64(v___x_1664_, sizeof(void*)*1, v___x_1665_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1664_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson(lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1676_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_x_1675_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1679_);
v___x_1682_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1683_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1681_, v___x_1682_);
v___x_1684_ = l_Lean_Json_mkObj(v___x_1683_);
lean_dec(v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(lean_object* v_j_1687_, lean_object* v_k_1688_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = l_Lean_Json_getObjValD(v_j_1687_, v_k_1688_);
v___x_1690_ = l_Lean_Json_getStr_x3f(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0___boxed(lean_object* v_j_1691_, lean_object* v_k_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_j_1691_, v_k_1692_);
lean_dec_ref(v_k_1692_);
return v_res_1693_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = 1;
v___x_1700_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1));
v___x_1701_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_1703_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2);
v___x_1704_ = lean_string_append(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = 1;
v___x_1708_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4));
v___x_1709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1708_, v___x_1707_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5);
v___x_1711_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3);
v___x_1712_ = lean_string_append(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1714_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6);
v___x_1715_ = lean_string_append(v___x_1714_, v___x_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson(lean_object* v_json_1716_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1718_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_1716_, v___x_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1728_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1723_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7);
v___x_1724_ = lean_string_append(v___x_1723_, v_a_1719_);
lean_dec(v_a_1719_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1724_);
v___x_1726_ = v___x_1721_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
else
{
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_a_1729_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1718_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1718_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 0);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1718_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1718_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object* v___y_1747_){
_start:
{
lean_object* v_doc_1749_; lean_object* v___x_1750_; 
v_doc_1749_ = lean_ctor_get(v___y_1747_, 1);
lean_inc_ref(v_doc_1749_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_doc_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1751_);
lean_dec_ref(v___y_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t v_k_1754_, lean_object* v_t_1755_){
_start:
{
if (lean_obj_tag(v_t_1755_) == 0)
{
lean_object* v_k_1756_; lean_object* v_l_1757_; lean_object* v_r_1758_; uint64_t v___x_1759_; uint8_t v___x_1760_; 
v_k_1756_ = lean_ctor_get(v_t_1755_, 1);
v_l_1757_ = lean_ctor_get(v_t_1755_, 3);
v_r_1758_ = lean_ctor_get(v_t_1755_, 4);
v___x_1759_ = lean_unbox_uint64(v_k_1756_);
v___x_1760_ = lean_uint64_dec_lt(v_k_1754_, v___x_1759_);
if (v___x_1760_ == 0)
{
uint64_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_unbox_uint64(v_k_1756_);
v___x_1762_ = lean_uint64_dec_eq(v_k_1754_, v___x_1761_);
if (v___x_1762_ == 0)
{
v_t_1755_ = v_r_1758_;
goto _start;
}
else
{
return v___x_1762_;
}
}
else
{
v_t_1755_ = v_l_1757_;
goto _start;
}
}
else
{
uint8_t v___x_1765_; 
v___x_1765_ = 0;
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object* v_k_1766_, lean_object* v_t_1767_){
_start:
{
uint64_t v_k_boxed_1768_; uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_k_boxed_1768_ = lean_unbox_uint64(v_k_1766_);
lean_dec_ref(v_k_1766_);
v_res_1769_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_boxed_1768_, v_t_1767_);
lean_dec(v_t_1767_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object* v___x_1771_, uint64_t v_hash_1772_, lean_object* v_s_1773_){
_start:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1773_);
v___x_1775_ = lean_nat_dec_le(v___x_1771_, v___x_1774_);
lean_dec(v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v_toEnvExtension_1777_; lean_object* v_asyncMode_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1776_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1777_ = lean_ctor_get(v___x_1776_, 0);
v_asyncMode_1778_ = lean_ctor_get(v_toEnvExtension_1777_, 2);
v___x_1779_ = lean_box(1);
v___x_1780_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_1773_);
v___x_1781_ = lean_box(0);
v___x_1782_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1779_, v___x_1776_, v___x_1780_, v_asyncMode_1778_, v___x_1781_);
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_hash_1772_, v___x_1782_);
lean_dec(v___x_1782_);
return v___x_1783_;
}
else
{
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object* v___x_1784_, lean_object* v_hash_1785_, lean_object* v_s_1786_){
_start:
{
uint64_t v_hash_boxed_1787_; uint8_t v_res_1788_; lean_object* v_r_1789_; 
v_hash_boxed_1787_ = lean_unbox_uint64(v_hash_1785_);
lean_dec_ref(v_hash_1785_);
v_res_1788_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1784_, v_hash_boxed_1787_, v_s_1786_);
lean_dec_ref(v_s_1786_);
lean_dec(v___x_1784_);
v_r_1789_ = lean_box(v_res_1788_);
return v_r_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object* v___x_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1790_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object* v___x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1794_, v___y_1795_);
lean_dec_ref(v___y_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object* v_snd_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_snd_1798_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1817_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_javascript_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v_javascript_1812_ = lean_ctor_get(v_a_1808_, 0);
lean_inc_ref(v_javascript_1812_);
lean_dec(v_a_1808_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_javascript_1812_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1813_);
v___x_1815_ = v___x_1810_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_a_1818_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1807_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1807_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object* v_snd_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t v_hash_1836_, lean_object* v___x_1837_, lean_object* v_snap_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v_toEnvExtension_1842_; lean_object* v_asyncMode_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1841_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1842_ = lean_ctor_get(v___x_1841_, 0);
v_asyncMode_1843_ = lean_ctor_get(v_toEnvExtension_1842_, 2);
v___x_1844_ = lean_box(1);
v___x_1845_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1838_);
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1844_, v___x_1841_, v___x_1845_, v_asyncMode_1843_, v___x_1846_);
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1847_, v_hash_1836_);
lean_dec(v___x_1847_);
if (lean_obj_tag(v___x_1848_) == 1)
{
lean_object* v_val_1849_; lean_object* v_snd_1850_; lean_object* v___f_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v___x_1837_);
v_val_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v_snd_1850_ = lean_ctor_get(v_val_1849_, 1);
lean_inc(v_snd_1850_);
lean_dec(v_val_1849_);
v___f_1851_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__2___boxed), 9, 1);
lean_closure_set(v___f_1851_, 0, v_snd_1850_);
v___x_1852_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1838_, v___f_1851_, v___y_1839_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; 
lean_dec(v___x_1848_);
lean_dec_ref(v_snap_1838_);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1837_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object* v_hash_1854_, lean_object* v___x_1855_, lean_object* v_snap_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint64_t v_hash_boxed_1859_; lean_object* v_res_1860_; 
v_hash_boxed_1859_ = lean_unbox_uint64(v_hash_1854_);
lean_dec_ref(v_hash_1854_);
v_res_1860_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_boxed_1859_, v___x_1855_, v_snap_1856_, v___y_1857_);
lean_dec_ref(v___y_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource(lean_object* v_args_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint64_t v_hash_1868_; lean_object* v_pos_1869_; lean_object* v___x_1870_; 
v___x_1866_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1867_ = lean_st_ref_get(v___x_1866_);
v_hash_1868_ = lean_ctor_get_uint64(v_args_1863_, sizeof(void*)*1);
v_pos_1869_ = lean_ctor_get(v_args_1863_, 0);
lean_inc_ref(v_pos_1869_);
lean_dec_ref(v_args_1863_);
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_1867_, v_hash_1868_);
lean_dec(v___x_1867_);
if (lean_obj_tag(v___x_1870_) == 1)
{
lean_object* v_val_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_pos_1869_);
v_val_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1882_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_val_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1882_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_snd_1875_; lean_object* v_javascript_1876_; lean_object* v___x_1878_; 
v_snd_1875_ = lean_ctor_get(v_val_1871_, 1);
lean_inc(v_snd_1875_);
lean_dec(v_val_1871_);
v_javascript_1876_ = lean_ctor_get(v_snd_1875_, 0);
lean_inc_ref(v_javascript_1876_);
lean_dec(v_snd_1875_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_javascript_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_javascript_1876_);
v___x_1878_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_task_pure(v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v_toEditableDocumentCore_1885_; lean_object* v_meta_1886_; lean_object* v_text_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; 
lean_dec(v___x_1870_);
v___x_1883_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_1864_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v_toEditableDocumentCore_1885_ = lean_ctor_get(v_a_1884_, 0);
v_meta_1886_ = lean_ctor_get(v_toEditableDocumentCore_1885_, 0);
v_text_1887_ = lean_ctor_get(v_meta_1886_, 3);
v___x_1888_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1887_, v_pos_1869_);
v___x_1889_ = lean_box_uint64(v_hash_1868_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1890_, 0, v___x_1888_);
lean_closure_set(v___f_1890_, 1, v___x_1889_);
v___x_1891_ = 3;
v___x_1892_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_1893_ = lean_uint64_to_nat(v_hash_1868_);
v___x_1894_ = l_Nat_reprFast(v___x_1893_);
v___x_1895_ = lean_string_append(v___x_1892_, v___x_1894_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_1897_ = lean_string_append(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*1, v___x_1891_);
lean_inc_ref(v___x_1898_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1899_, 0, v___x_1898_);
v___x_1900_ = lean_box_uint64(v_hash_1868_);
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1901_, 0, v___x_1900_);
lean_closure_set(v___f_1901_, 1, v___x_1898_);
v___x_1902_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1884_, v___f_1890_, v___f_1899_, v___f_1901_, v_a_1864_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object* v_args_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Widget_getWidgetSource(v_args_1903_, v_a_1904_);
lean_dec_ref(v_a_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object* v_00_u03b2_1907_, uint64_t v_k_1908_, lean_object* v_t_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1908_, v_t_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object* v_00_u03b2_1911_, lean_object* v_k_1912_, lean_object* v_t_1913_){
_start:
{
uint64_t v_k_boxed_1914_; uint8_t v_res_1915_; lean_object* v_r_1916_; 
v_k_boxed_1914_ = lean_unbox_uint64(v_k_1912_);
lean_dec_ref(v_k_1912_);
v_res_1915_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(v_00_u03b2_1911_, v_k_boxed_1914_, v_t_1913_);
lean_dec(v_t_1913_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_1917_, lean_object* v_i_1918_, lean_object* v_k_1919_){
_start:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = lean_array_get_size(v_keys_1917_);
v___x_1921_ = lean_nat_dec_lt(v_i_1918_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_dec(v_i_1918_);
return v___x_1921_;
}
else
{
lean_object* v_k_x27_1922_; uint8_t v___x_1923_; 
v_k_x27_1922_ = lean_array_fget_borrowed(v_keys_1917_, v_i_1918_);
v___x_1923_ = lean_name_eq(v_k_1919_, v_k_x27_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_add(v_i_1918_, v___x_1924_);
lean_dec(v_i_1918_);
v_i_1918_ = v___x_1925_;
goto _start;
}
else
{
lean_dec(v_i_1918_);
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_1927_, lean_object* v_i_1928_, lean_object* v_k_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1927_, v_i_1928_, v_k_1929_);
lean_dec(v_k_1929_);
lean_dec_ref(v_keys_1927_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_1932_, size_t v_x_1933_, lean_object* v_x_1934_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_object* v_es_1935_; lean_object* v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; lean_object* v_j_1939_; lean_object* v___x_1940_; 
v_es_1935_ = lean_ctor_get(v_x_1932_, 0);
v___x_1936_ = lean_box(2);
v___x_1937_ = ((size_t)31ULL);
v___x_1938_ = lean_usize_land(v_x_1933_, v___x_1937_);
v_j_1939_ = lean_usize_to_nat(v___x_1938_);
v___x_1940_ = lean_array_get_borrowed(v___x_1936_, v_es_1935_, v_j_1939_);
lean_dec(v_j_1939_);
switch(lean_obj_tag(v___x_1940_))
{
case 0:
{
lean_object* v_key_1941_; uint8_t v___x_1942_; 
v_key_1941_ = lean_ctor_get(v___x_1940_, 0);
v___x_1942_ = lean_name_eq(v_x_1934_, v_key_1941_);
return v___x_1942_;
}
case 1:
{
lean_object* v_node_1943_; size_t v___x_1944_; size_t v___x_1945_; 
v_node_1943_ = lean_ctor_get(v___x_1940_, 0);
v___x_1944_ = ((size_t)5ULL);
v___x_1945_ = lean_usize_shift_right(v_x_1933_, v___x_1944_);
v_x_1932_ = v_node_1943_;
v_x_1933_ = v___x_1945_;
goto _start;
}
default: 
{
uint8_t v___x_1947_; 
v___x_1947_ = 0;
return v___x_1947_;
}
}
}
else
{
lean_object* v_ks_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v_ks_1948_ = lean_ctor_get(v_x_1932_, 0);
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_1948_, v___x_1949_, v_x_1934_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
size_t v_x_1054__boxed_1954_; uint8_t v_res_1955_; lean_object* v_r_1956_; 
v_x_1054__boxed_1954_ = lean_unbox_usize(v_x_1952_);
lean_dec(v_x_1952_);
v_res_1955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1951_, v_x_1054__boxed_1954_, v_x_1953_);
lean_dec(v_x_1953_);
lean_dec_ref(v_x_1951_);
v_r_1956_ = lean_box(v_res_1955_);
return v_r_1956_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1957_; uint64_t v___x_1958_; 
v___x_1957_ = lean_unsigned_to_nat(1723u);
v___x_1958_ = lean_uint64_of_nat(v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
uint64_t v___y_1962_; 
if (lean_obj_tag(v_x_1960_) == 0)
{
uint64_t v___x_1965_; 
v___x_1965_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_1962_ = v___x_1965_;
goto v___jp_1961_;
}
else
{
uint64_t v_hash_1966_; 
v_hash_1966_ = lean_ctor_get_uint64(v_x_1960_, sizeof(void*)*2);
v___y_1962_ = v_hash_1966_;
goto v___jp_1961_;
}
v___jp_1961_:
{
size_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = lean_uint64_to_usize(v___y_1962_);
v___x_1964_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1959_, v___x_1963_, v_x_1960_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1967_, v_x_1968_);
lean_dec(v_x_1968_);
lean_dec_ref(v_x_1967_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
lean_object* v_ks_1975_; lean_object* v_vs_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2000_; 
v_ks_1975_ = lean_ctor_get(v_x_1971_, 0);
v_vs_1976_ = lean_ctor_get(v_x_1971_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1971_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1978_ = v_x_1971_;
v_isShared_1979_ = v_isSharedCheck_2000_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_vs_1976_);
lean_inc(v_ks_1975_);
lean_dec(v_x_1971_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2000_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = lean_array_get_size(v_ks_1975_);
v___x_1981_ = lean_nat_dec_lt(v_x_1972_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v_x_1972_);
v___x_1982_ = lean_array_push(v_ks_1975_, v_x_1973_);
v___x_1983_ = lean_array_push(v_vs_1976_, v_x_1974_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___x_1983_);
lean_ctor_set(v___x_1978_, 0, v___x_1982_);
v___x_1985_ = v___x_1978_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
lean_object* v_k_x27_1987_; uint8_t v___x_1988_; 
v_k_x27_1987_ = lean_array_fget_borrowed(v_ks_1975_, v_x_1972_);
v___x_1988_ = lean_name_eq(v_x_1973_, v_k_x27_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1990_; 
if (v_isShared_1979_ == 0)
{
v___x_1990_ = v___x_1978_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_ks_1975_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_vs_1976_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = lean_nat_add(v_x_1972_, v___x_1991_);
lean_dec(v_x_1972_);
v_x_1971_ = v___x_1990_;
v_x_1972_ = v___x_1992_;
goto _start;
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1995_ = lean_array_fset(v_ks_1975_, v_x_1972_, v_x_1973_);
v___x_1996_ = lean_array_fset(v_vs_1976_, v_x_1972_, v_x_1974_);
lean_dec(v_x_1972_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___x_1996_);
lean_ctor_set(v___x_1978_, 0, v___x_1995_);
v___x_1998_ = v___x_1978_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_n_2001_, lean_object* v_k_2002_, lean_object* v_v_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_n_2001_, v___x_2004_, v_k_2002_, v_v_2003_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_x_2007_, size_t v_x_2008_, size_t v_x_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 0)
{
lean_object* v_es_2012_; size_t v___x_2013_; size_t v___x_2014_; lean_object* v_j_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v_es_2012_ = lean_ctor_get(v_x_2007_, 0);
v___x_2013_ = ((size_t)31ULL);
v___x_2014_ = lean_usize_land(v_x_2008_, v___x_2013_);
v_j_2015_ = lean_usize_to_nat(v___x_2014_);
v___x_2016_ = lean_array_get_size(v_es_2012_);
v___x_2017_ = lean_nat_dec_lt(v_j_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_dec(v_j_2015_);
lean_dec(v_x_2011_);
lean_dec(v_x_2010_);
return v_x_2007_;
}
else
{
lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2056_; 
lean_inc_ref(v_es_2012_);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_2007_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_x_2007_, 0);
lean_dec(v_unused_2057_);
v___x_2019_ = v_x_2007_;
v_isShared_2020_ = v_isSharedCheck_2056_;
goto v_resetjp_2018_;
}
else
{
lean_dec(v_x_2007_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2056_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_v_2021_; lean_object* v___x_2022_; lean_object* v_xs_x27_2023_; lean_object* v___y_2025_; 
v_v_2021_ = lean_array_fget(v_es_2012_, v_j_2015_);
v___x_2022_ = lean_box(0);
v_xs_x27_2023_ = lean_array_fset(v_es_2012_, v_j_2015_, v___x_2022_);
switch(lean_obj_tag(v_v_2021_))
{
case 0:
{
lean_object* v_key_2030_; lean_object* v_val_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2041_; 
v_key_2030_ = lean_ctor_get(v_v_2021_, 0);
v_val_2031_ = lean_ctor_get(v_v_2021_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_v_2021_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2033_ = v_v_2021_;
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_val_2031_);
lean_inc(v_key_2030_);
lean_dec(v_v_2021_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_name_eq(v_x_2010_, v_key_2030_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_del_object(v___x_2033_);
v___x_2036_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2030_, v_val_2031_, v_x_2010_, v_x_2011_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___y_2025_ = v___x_2037_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2039_; 
lean_dec(v_val_2031_);
lean_dec(v_key_2030_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_x_2011_);
lean_ctor_set(v___x_2033_, 0, v_x_2010_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_x_2010_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_x_2011_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
v___y_2025_ = v___x_2039_;
goto v___jp_2024_;
}
}
}
}
case 1:
{
lean_object* v_node_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2054_; 
v_node_2042_ = lean_ctor_get(v_v_2021_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_v_2021_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2044_ = v_v_2021_;
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_node_2042_);
lean_dec(v_v_2021_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
size_t v___x_2046_; size_t v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2046_ = ((size_t)5ULL);
v___x_2047_ = lean_usize_shift_right(v_x_2008_, v___x_2046_);
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_x_2009_, v___x_2048_);
v___x_2050_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_node_2042_, v___x_2047_, v___x_2049_, v_x_2010_, v_x_2011_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2050_);
v___x_2052_ = v___x_2044_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
v___y_2025_ = v___x_2052_;
goto v___jp_2024_;
}
}
}
default: 
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_x_2010_);
lean_ctor_set(v___x_2055_, 1, v_x_2011_);
v___y_2025_ = v___x_2055_;
goto v___jp_2024_;
}
}
v___jp_2024_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_array_fset(v_xs_x27_2023_, v_j_2015_, v___y_2025_);
lean_dec(v_j_2015_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2026_);
v___x_2028_ = v___x_2019_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
else
{
lean_object* v_ks_2058_; lean_object* v_vs_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2079_; 
v_ks_2058_ = lean_ctor_get(v_x_2007_, 0);
v_vs_2059_ = lean_ctor_get(v_x_2007_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_x_2007_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2061_ = v_x_2007_;
v_isShared_2062_ = v_isSharedCheck_2079_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_vs_2059_);
lean_inc(v_ks_2058_);
lean_dec(v_x_2007_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2079_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_ks_2058_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_vs_2059_);
v___x_2064_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v_newNode_2065_; uint8_t v___y_2067_; size_t v___x_2073_; uint8_t v___x_2074_; 
v_newNode_2065_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v___x_2064_, v_x_2010_, v_x_2011_);
v___x_2073_ = ((size_t)7ULL);
v___x_2074_ = lean_usize_dec_le(v___x_2073_, v_x_2009_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2065_);
v___x_2076_ = lean_unsigned_to_nat(4u);
v___x_2077_ = lean_nat_dec_lt(v___x_2075_, v___x_2076_);
lean_dec(v___x_2075_);
v___y_2067_ = v___x_2077_;
goto v___jp_2066_;
}
else
{
v___y_2067_ = v___x_2074_;
goto v___jp_2066_;
}
v___jp_2066_:
{
if (v___y_2067_ == 0)
{
lean_object* v_ks_2068_; lean_object* v_vs_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_ks_2068_ = lean_ctor_get(v_newNode_2065_, 0);
lean_inc_ref(v_ks_2068_);
v_vs_2069_ = lean_ctor_get(v_newNode_2065_, 1);
lean_inc_ref(v_vs_2069_);
lean_dec_ref(v_newNode_2065_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0);
v___x_2072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_x_2009_, v_ks_2068_, v_vs_2069_, v___x_2070_, v___x_2071_);
lean_dec_ref(v_vs_2069_);
lean_dec_ref(v_ks_2068_);
return v___x_2072_;
}
else
{
return v_newNode_2065_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t v_depth_2080_, lean_object* v_keys_2081_, lean_object* v_vals_2082_, lean_object* v_i_2083_, lean_object* v_entries_2084_){
_start:
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_array_get_size(v_keys_2081_);
v___x_2086_ = lean_nat_dec_lt(v_i_2083_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v_i_2083_);
return v_entries_2084_;
}
else
{
lean_object* v_k_2087_; lean_object* v_v_2088_; uint64_t v___y_2090_; 
v_k_2087_ = lean_array_fget_borrowed(v_keys_2081_, v_i_2083_);
v_v_2088_ = lean_array_fget_borrowed(v_vals_2082_, v_i_2083_);
if (lean_obj_tag(v_k_2087_) == 0)
{
uint64_t v___x_2101_; 
v___x_2101_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_2090_ = v___x_2101_;
goto v___jp_2089_;
}
else
{
uint64_t v_hash_2102_; 
v_hash_2102_ = lean_ctor_get_uint64(v_k_2087_, sizeof(void*)*2);
v___y_2090_ = v_hash_2102_;
goto v___jp_2089_;
}
v___jp_2089_:
{
size_t v_h_2091_; size_t v___x_2092_; lean_object* v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; size_t v_h_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_h_2091_ = lean_uint64_to_usize(v___y_2090_);
v___x_2092_ = ((size_t)5ULL);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_sub(v_depth_2080_, v___x_2094_);
v___x_2096_ = lean_usize_mul(v___x_2092_, v___x_2095_);
v_h_2097_ = lean_usize_shift_right(v_h_2091_, v___x_2096_);
v___x_2098_ = lean_nat_add(v_i_2083_, v___x_2093_);
lean_dec(v_i_2083_);
lean_inc(v_v_2088_);
lean_inc(v_k_2087_);
v___x_2099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_entries_2084_, v_h_2097_, v_depth_2080_, v_k_2087_, v_v_2088_);
v_i_2083_ = v___x_2098_;
v_entries_2084_ = v___x_2099_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_depth_2103_, lean_object* v_keys_2104_, lean_object* v_vals_2105_, lean_object* v_i_2106_, lean_object* v_entries_2107_){
_start:
{
size_t v_depth_boxed_2108_; lean_object* v_res_2109_; 
v_depth_boxed_2108_ = lean_unbox_usize(v_depth_2103_);
lean_dec(v_depth_2103_);
v_res_2109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_boxed_2108_, v_keys_2104_, v_vals_2105_, v_i_2106_, v_entries_2107_);
lean_dec_ref(v_vals_2105_);
lean_dec_ref(v_keys_2104_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_){
_start:
{
size_t v_x_1198__boxed_2115_; size_t v_x_1199__boxed_2116_; lean_object* v_res_2117_; 
v_x_1198__boxed_2115_ = lean_unbox_usize(v_x_2111_);
lean_dec(v_x_2111_);
v_x_1199__boxed_2116_ = lean_unbox_usize(v_x_2112_);
lean_dec(v_x_2112_);
v_res_2117_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2110_, v_x_1198__boxed_2115_, v_x_1199__boxed_2116_, v_x_2113_, v_x_2114_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_2118_, lean_object* v_x_2119_, lean_object* v_x_2120_){
_start:
{
uint64_t v___y_2122_; 
if (lean_obj_tag(v_x_2119_) == 0)
{
uint64_t v___x_2126_; 
v___x_2126_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___y_2122_ = v___x_2126_;
goto v___jp_2121_;
}
else
{
uint64_t v_hash_2127_; 
v_hash_2127_ = lean_ctor_get_uint64(v_x_2119_, sizeof(void*)*2);
v___y_2122_ = v_hash_2127_;
goto v___jp_2121_;
}
v___jp_2121_:
{
size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_uint64_to_usize(v___y_2122_);
v___x_2124_ = ((size_t)1ULL);
v___x_2125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2118_, v___x_2123_, v___x_2124_, v_x_2119_, v_x_2120_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v___y_2128_){
_start:
{
lean_inc(v___y_2128_);
return v___y_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(v___y_2129_);
lean_dec(v___y_2129_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object* v_expireTime_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_x_2132_);
lean_ctor_set(v___x_2133_, 1, v_expireTime_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object* v_val_2134_, lean_object* v___f_2135_, lean_object* v_x_2136_, lean_object* v___y_2137_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v___f_2135_);
v_a_2139_ = lean_ctor_get(v_x_2136_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v_x_2136_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v_x_2136_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 1);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2170_; 
v_a_2147_ = lean_ctor_get(v_x_2136_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2149_ = v_x_2136_;
v_isShared_2150_ = v_isSharedCheck_2170_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v_x_2136_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2170_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v_objects_2152_; lean_object* v_expireTime_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2169_; 
v___x_2151_ = lean_st_ref_take(v_val_2134_);
v_objects_2152_ = lean_ctor_get(v___x_2151_, 0);
v_expireTime_2153_ = lean_ctor_get(v___x_2151_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2155_ = v___x_2151_;
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_expireTime_2153_);
lean_inc(v_objects_2152_);
lean_dec(v___x_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___f_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_2157_, 0, v_expireTime_2153_);
v___x_2158_ = l_Lean_Widget_instToJsonWidgetSource_toJson(v_a_2147_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_objects_2152_);
lean_ctor_set(v___x_2155_, 0, v___x_2158_);
v___x_2160_ = v___x_2155_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_objects_2152_);
v___x_2160_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v_fst_2162_; lean_object* v_snd_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2161_ = l_Prod_map___redArg(v___f_2135_, v___f_2157_, v___x_2160_);
v_fst_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_fst_2162_);
v_snd_2163_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_snd_2163_);
lean_dec_ref(v___x_2161_);
v___x_2164_ = lean_st_ref_set(v_val_2134_, v_snd_2163_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set_tag(v___x_2149_, 0);
lean_ctor_set(v___x_2149_, 0, v_fst_2162_);
v___x_2166_ = v___x_2149_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_fst_2162_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object* v_val_2171_, lean_object* v___f_2172_, lean_object* v_x_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2171_, v___f_2172_, v_x_2173_, v___y_2174_);
lean_dec_ref(v___y_2174_);
lean_dec(v_val_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object* v_method_2184_, lean_object* v_handler_2185_, lean_object* v___f_2186_, uint64_t v_seshId_2187_, lean_object* v_j_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_rpcSessions_2191_; lean_object* v___x_2192_; 
v_rpcSessions_2191_ = lean_ctor_get(v___y_2189_, 0);
v___x_2192_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_2191_, v_seshId_2187_);
if (lean_obj_tag(v___x_2192_) == 1)
{
lean_object* v_val_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_val_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = lean_st_ref_get(v_val_2193_);
lean_dec(v___x_2194_);
lean_inc(v_j_2188_);
v___x_2195_ = l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(v_j_2188_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_val_2193_);
lean_dec_ref(v___f_2186_);
lean_dec_ref(v_handler_2185_);
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2216_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2216_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
uint8_t v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2200_ = 3;
v___x_2201_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_2202_ = 1;
v___x_2203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2184_, v___x_2202_);
v___x_2204_ = lean_string_append(v___x_2201_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_2206_ = lean_string_append(v___x_2204_, v___x_2205_);
v___x_2207_ = l_Lean_Json_compress(v_j_2188_);
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_2210_ = lean_string_append(v___x_2208_, v___x_2209_);
v___x_2211_ = lean_string_append(v___x_2210_, v_a_2196_);
lean_dec(v_a_2196_);
v___x_2212_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*1, v___x_2200_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 1);
lean_ctor_set(v___x_2198_, 0, v___x_2212_);
v___x_2214_ = v___x_2198_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
lean_dec(v_j_2188_);
lean_dec(v_method_2184_);
v_a_2217_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2195_, 1);
lean_inc_ref(v___y_2189_);
v___x_2218_ = lean_apply_3(v_handler_2185_, v_a_2217_, v___y_2189_, lean_box(0));
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___f_2220_; lean_object* v___x_2221_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___f_2220_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2220_, 0, v_val_2193_);
lean_closure_set(v___f_2220_, 1, v___f_2186_);
v___x_2221_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_2219_, v___f_2220_, v___y_2189_);
return v___x_2221_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_val_2193_);
lean_dec_ref(v___f_2186_);
v_a_2222_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2218_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2218_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v___x_2192_);
lean_dec(v_j_2188_);
lean_dec_ref(v___f_2186_);
lean_dec_ref(v_handler_2185_);
lean_dec(v_method_2184_);
v___x_2230_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object* v_method_2232_, lean_object* v_handler_2233_, lean_object* v___f_2234_, lean_object* v_seshId_2235_, lean_object* v_j_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
uint64_t v_seshId_boxed_2239_; lean_object* v_res_2240_; 
v_seshId_boxed_2239_ = lean_unbox_uint64(v_seshId_2235_);
lean_dec_ref(v_seshId_2235_);
v_res_2240_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v_method_2232_, v_handler_2233_, v___f_2234_, v_seshId_boxed_2239_, v_j_2236_, v___y_2237_);
lean_dec_ref(v___y_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_method_2242_, lean_object* v_handler_2243_){
_start:
{
lean_object* v___f_2244_; lean_object* v___f_2245_; 
v___f_2244_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed), 7, 3);
lean_closure_set(v___f_2245_, 0, v_method_2242_);
lean_closure_set(v___f_2245_, 1, v_handler_2243_);
lean_closure_set(v___f_2245_, 2, v___f_2244_);
return v___f_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object* v_method_2250_, lean_object* v_handler_2251_){
_start:
{
uint8_t v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_errMsg_2259_; 
v___x_2253_ = l_Lean_initializing();
v___x_2254_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_2255_ = 1;
lean_inc(v_method_2250_);
v___x_2256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2250_, v___x_2255_);
v___x_2257_ = lean_string_append(v___x_2254_, v___x_2256_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v_handler_2251_);
lean_dec(v_method_2250_);
v___x_2260_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_2261_ = lean_string_append(v_errMsg_2259_, v___x_2260_);
v___x_2262_ = lean_mk_io_user_error(v___x_2261_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2264_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_2265_ = lean_st_ref_get(v___x_2264_);
v___x_2266_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2265_, v_method_2250_);
lean_dec(v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec_ref(v_errMsg_2259_);
v___x_2267_ = lean_st_ref_take(v___x_2264_);
lean_inc(v_method_2250_);
v___x_2268_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(v_method_2250_, v_handler_2251_);
v___x_2269_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2267_, v_method_2250_, v___x_2268_);
v___x_2270_ = lean_st_ref_set(v___x_2264_, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec_ref(v_handler_2251_);
lean_dec(v_method_2250_);
v___x_2272_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_2273_ = lean_string_append(v_errMsg_2259_, v___x_2272_);
v___x_2274_ = lean_mk_io_user_error(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2276_, lean_object* v_handler_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2276_, v_handler_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2288_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2289_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v___x_2287_, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
return v_res_2291_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2293_, v_x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2296_, v_x_2297_, v_x_2298_);
lean_dec(v_x_2298_);
lean_dec_ref(v_x_2297_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_2301_){
_start:
{
lean_inc_ref(v_x_2301_);
return v_x_2301_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2302_);
lean_dec_ref(v_x_2302_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2304_, lean_object* v_x_2305_, lean_object* v___y_2306_){
_start:
{
lean_inc_ref(v_x_2305_);
return v_x_2305_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b1_2307_, v_x_2308_, v___y_2309_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_x_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2312_, v_x_2313_, v_x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2316_, lean_object* v_x_2317_, size_t v_x_2318_, lean_object* v_x_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2317_, v_x_2318_, v_x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
size_t v_x_1689__boxed_2325_; uint8_t v_res_2326_; lean_object* v_r_2327_; 
v_x_1689__boxed_2325_ = lean_unbox_usize(v_x_2323_);
lean_dec(v_x_2323_);
v_res_2326_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2321_, v_x_2322_, v_x_1689__boxed_2325_, v_x_2324_);
lean_dec(v_x_2324_);
lean_dec_ref(v_x_2322_);
v_r_2327_ = lean_box(v_res_2326_);
return v_r_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2328_, lean_object* v_x_2329_, size_t v_x_2330_, size_t v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2329_, v_x_2330_, v_x_2331_, v_x_2332_, v_x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
size_t v_x_1700__boxed_2341_; size_t v_x_1701__boxed_2342_; lean_object* v_res_2343_; 
v_x_1700__boxed_2341_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_x_1701__boxed_2342_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_2335_, v_x_2336_, v_x_1700__boxed_2341_, v_x_1701__boxed_2342_, v_x_2339_, v_x_2340_);
return v_res_2343_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2344_, lean_object* v_keys_2345_, lean_object* v_vals_2346_, lean_object* v_heq_2347_, lean_object* v_i_2348_, lean_object* v_k_2349_){
_start:
{
uint8_t v___x_2350_; 
v___x_2350_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2345_, v_i_2348_, v_k_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2351_, lean_object* v_keys_2352_, lean_object* v_vals_2353_, lean_object* v_heq_2354_, lean_object* v_i_2355_, lean_object* v_k_2356_){
_start:
{
uint8_t v_res_2357_; lean_object* v_r_2358_; 
v_res_2357_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2351_, v_keys_2352_, v_vals_2353_, v_heq_2354_, v_i_2355_, v_k_2356_);
lean_dec(v_k_2356_);
lean_dec_ref(v_vals_2353_);
lean_dec_ref(v_keys_2352_);
v_r_2358_ = lean_box(v_res_2357_);
return v_r_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_2359_, lean_object* v_n_2360_, lean_object* v_k_2361_, lean_object* v_v_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v_n_2360_, v_k_2361_, v_v_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2364_, size_t v_depth_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_entries_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2365_, v_keys_2366_, v_vals_2367_, v_i_2369_, v_entries_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_depth_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_entries_2378_){
_start:
{
size_t v_depth_boxed_2379_; lean_object* v_res_2380_; 
v_depth_boxed_2379_ = lean_unbox_usize(v_depth_2373_);
lean_dec(v_depth_2373_);
v_res_2380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(v_00_u03b2_2372_, v_depth_boxed_2379_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_entries_2378_);
lean_dec_ref(v_vals_2375_);
lean_dec_ref(v_keys_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_x_2382_, v_x_2383_, v_x_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(lean_object* v_x_2387_){
_start:
{
if (lean_obj_tag(v_x_2387_) == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_unsigned_to_nat(0u);
return v___x_2388_;
}
else
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_unsigned_to_nat(1u);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___boxed(lean_object* v_x_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx(v_x_2390_);
lean_dec_ref(v_x_2390_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object* v_t_2392_, lean_object* v_k_2393_){
_start:
{
if (lean_obj_tag(v_t_2392_) == 0)
{
lean_object* v_n_2394_; lean_object* v___x_2395_; 
v_n_2394_ = lean_ctor_get(v_t_2392_, 0);
lean_inc(v_n_2394_);
lean_dec_ref_known(v_t_2392_, 1);
v___x_2395_ = lean_apply_1(v_k_2393_, v_n_2394_);
return v___x_2395_;
}
else
{
lean_object* v_wi_2396_; lean_object* v___x_2397_; 
v_wi_2396_ = lean_ctor_get(v_t_2392_, 0);
lean_inc_ref(v_wi_2396_);
lean_dec_ref_known(v_t_2392_, 1);
v___x_2397_ = lean_apply_1(v_k_2393_, v_wi_2396_);
return v___x_2397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object* v_motive_2398_, lean_object* v_ctorIdx_2399_, lean_object* v_t_2400_, lean_object* v_h_2401_, lean_object* v_k_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2400_, v_k_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object* v_motive_2404_, lean_object* v_ctorIdx_2405_, lean_object* v_t_2406_, lean_object* v_h_2407_, lean_object* v_k_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(v_motive_2404_, v_ctorIdx_2405_, v_t_2406_, v_h_2407_, v_k_2408_);
lean_dec(v_ctorIdx_2405_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object* v_t_2410_, lean_object* v_global_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2410_, v_global_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object* v_motive_2413_, lean_object* v_t_2414_, lean_object* v_h_2415_, lean_object* v_global_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2414_, v_global_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object* v_t_2418_, lean_object* v_local_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2418_, v_local_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object* v_motive_2421_, lean_object* v_t_2422_, lean_object* v_h_2423_, lean_object* v_local_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2422_, v_local_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2426_, uint64_t v_k_2427_, lean_object* v_fallback_2428_){
_start:
{
if (lean_obj_tag(v_t_2426_) == 0)
{
lean_object* v_k_2429_; lean_object* v_v_2430_; lean_object* v_l_2431_; lean_object* v_r_2432_; uint64_t v___x_2433_; uint8_t v___x_2434_; 
v_k_2429_ = lean_ctor_get(v_t_2426_, 1);
v_v_2430_ = lean_ctor_get(v_t_2426_, 2);
v_l_2431_ = lean_ctor_get(v_t_2426_, 3);
v_r_2432_ = lean_ctor_get(v_t_2426_, 4);
v___x_2433_ = lean_unbox_uint64(v_k_2429_);
v___x_2434_ = lean_uint64_dec_lt(v_k_2427_, v___x_2433_);
if (v___x_2434_ == 0)
{
uint64_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = lean_unbox_uint64(v_k_2429_);
v___x_2436_ = lean_uint64_dec_eq(v_k_2427_, v___x_2435_);
if (v___x_2436_ == 0)
{
v_t_2426_ = v_r_2432_;
goto _start;
}
else
{
lean_inc(v_v_2430_);
return v_v_2430_;
}
}
else
{
v_t_2426_ = v_l_2431_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2428_);
return v_fallback_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2439_, lean_object* v_k_2440_, lean_object* v_fallback_2441_){
_start:
{
uint64_t v_k_boxed_2442_; lean_object* v_res_2443_; 
v_k_boxed_2442_ = lean_unbox_uint64(v_k_2440_);
lean_dec_ref(v_k_2440_);
v_res_2443_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2439_, v_k_boxed_2442_, v_fallback_2441_);
lean_dec(v_fallback_2441_);
lean_dec(v_t_2439_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_s_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v_fst_2446_; lean_object* v_snd_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2460_; 
v_fst_2446_ = lean_ctor_get(v_x_2445_, 0);
v_snd_2447_ = lean_ctor_get(v_x_2445_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_x_2445_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2449_ = v_x_2445_;
v_isShared_2450_ = v_isSharedCheck_2460_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_snd_2447_);
lean_inc(v_fst_2446_);
lean_dec(v_x_2445_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2460_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint64_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_snd_2447_);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_unbox_uint64(v_fst_2446_);
v___x_2454_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_s_2444_, v___x_2453_, v___x_2452_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 1);
lean_ctor_set(v___x_2449_, 1, v___x_2454_);
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2456_ = v___x_2449_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
uint64_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_unbox_uint64(v_fst_2446_);
lean_dec(v_fst_2446_);
v___x_2458_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_2457_, v___x_2456_, v_s_2444_);
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_x_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_a_2462_);
lean_inc_ref_n(v___x_2463_, 2);
v___x_2464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
lean_ctor_set(v___x_2464_, 2, v___x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_x_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v_x_2465_, v_a_2466_);
lean_dec_ref(v_x_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v___y_2468_){
_start:
{
lean_inc(v___y_2468_);
return v___y_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v___y_2469_);
lean_dec(v___y_2469_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_));
v___x_2486_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2489_, lean_object* v_t_2490_, uint64_t v_k_2491_, lean_object* v_fallback_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2490_, v_k_2491_, v_fallback_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2494_, lean_object* v_t_2495_, lean_object* v_k_2496_, lean_object* v_fallback_2497_){
_start:
{
uint64_t v_k_boxed_2498_; lean_object* v_res_2499_; 
v_k_boxed_2498_ = lean_unbox_uint64(v_k_2496_);
lean_dec_ref(v_k_2496_);
v_res_2499_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(v_00_u03b4_2494_, v_t_2495_, v_k_boxed_2498_, v_fallback_2497_);
lean_dec(v_fallback_2497_);
lean_dec(v_t_2495_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(lean_object* v_as_x27_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
if (lean_obj_tag(v_as_x27_2500_) == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_b_2501_);
return v___x_2507_;
}
else
{
lean_object* v_head_2508_; 
v_head_2508_ = lean_ctor_get(v_as_x27_2500_, 0);
if (lean_obj_tag(v_head_2508_) == 0)
{
lean_object* v_tail_2509_; lean_object* v_n_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_tail_2509_ = lean_ctor_get(v_as_x27_2500_, 1);
v_n_2510_ = lean_ctor_get(v_head_2508_, 0);
v___x_2511_ = lean_box(0);
lean_inc(v_n_2510_);
v___x_2512_ = l_Lean_mkConst(v_n_2510_, v___x_2511_);
v___x_2513_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v___x_2512_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = lean_array_push(v_b_2501_, v_a_2514_);
v_as_x27_2500_ = v_tail_2509_;
v_b_2501_ = v___x_2515_;
goto _start;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_b_2501_);
v_a_2517_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2513_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2513_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_tail_2525_; lean_object* v_wi_2526_; lean_object* v___x_2527_; 
v_tail_2525_ = lean_ctor_get(v_as_x27_2500_, 1);
v_wi_2526_ = lean_ctor_get(v_head_2508_, 0);
lean_inc_ref(v_wi_2526_);
v___x_2527_ = lean_array_push(v_b_2501_, v_wi_2526_);
v_as_x27_2500_ = v_tail_2525_;
v_b_2501_ = v___x_2527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg___boxed(lean_object* v_as_x27_2529_, lean_object* v_b_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2529_, v_b_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v_as_x27_2529_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(lean_object* v_init_2537_, lean_object* v_x_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
if (lean_obj_tag(v_x_2538_) == 0)
{
lean_object* v_v_2544_; lean_object* v_l_2545_; lean_object* v_r_2546_; lean_object* v___x_2547_; 
v_v_2544_ = lean_ctor_get(v_x_2538_, 2);
v_l_2545_ = lean_ctor_get(v_x_2538_, 3);
v_r_2546_ = lean_ctor_get(v_x_2538_, 4);
v___x_2547_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2537_, v_l_2545_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v_a_2549_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_a_2549_);
lean_dec(v_a_2548_);
v___x_2550_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_v_2544_, v_a_2549_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v_init_2537_ = v_a_2551_;
v_x_2538_ = v_r_2546_;
goto _start;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_a_2553_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2550_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2550_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
return v___x_2547_;
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_init_2537_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1___boxed(lean_object* v_init_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2563_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v_x_2564_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets(lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v_env_2579_; lean_object* v___x_2580_; lean_object* v_ext_2581_; lean_object* v_toEnvExtension_2582_; lean_object* v_asyncMode_2583_; lean_object* v_ret_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2578_ = lean_st_ref_get(v_a_2576_);
v_env_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc_ref(v_env_2579_);
lean_dec(v___x_2578_);
v___x_2580_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v_ext_2581_ = lean_ctor_get(v___x_2580_, 1);
v_toEnvExtension_2582_ = lean_ctor_get(v_ext_2581_, 0);
v_asyncMode_2583_ = lean_ctor_get(v_toEnvExtension_2582_, 2);
v_ret_2584_ = ((lean_object*)(l_Lean_Widget_evalPanelWidgets___closed__0));
v___x_2585_ = lean_box(1);
v___x_2586_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2585_, v___x_2580_, v_env_2579_, v_asyncMode_2583_);
v___x_2587_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_ret_2584_, v___x_2586_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec(v___x_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2596_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_a_2592_; lean_object* v___x_2594_; 
v_a_2592_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_a_2592_);
lean_dec(v_a_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v_a_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
v_a_2597_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2587_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2587_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Widget_evalPanelWidgets(v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object* v_as_2611_, lean_object* v_as_x27_2612_, lean_object* v_b_2613_, lean_object* v_a_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2612_, v_b_2613_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object* v_as_2621_, lean_object* v_as_x27_2622_, lean_object* v_b_2623_, lean_object* v_a_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2621_, v_as_x27_2622_, v_b_2623_, v_a_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v_as_x27_2622_);
lean_dec(v_as_2621_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, uint64_t v_h_2634_, lean_object* v_n_2635_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2636_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2637_ = lean_box_uint64(v_h_2634_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v_n_2635_);
v___x_2639_ = 0;
v___x_2640_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2631_, v_inst_2633_, v_inst_2632_, v___x_2636_, v___x_2638_, v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_h_2644_, lean_object* v_n_2645_){
_start:
{
uint64_t v_h_boxed_2646_; lean_object* v_res_2647_; 
v_h_boxed_2646_ = lean_unbox_uint64(v_h_2644_);
lean_dec_ref(v_h_2644_);
v_res_2647_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2641_, v_inst_2642_, v_inst_2643_, v_h_boxed_2646_, v_n_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object* v_m_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, uint64_t v_h_2652_, lean_object* v_n_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2649_, v_inst_2650_, v_inst_2651_, v_h_2652_, v_n_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object* v_m_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_h_2659_, lean_object* v_n_2660_){
_start:
{
uint64_t v_h_boxed_2661_; lean_object* v_res_2662_; 
v_h_boxed_2661_ = lean_unbox_uint64(v_h_2659_);
lean_dec_ref(v_h_2659_);
v_res_2662_ = l_Lean_Widget_addPanelWidgetGlobal(v_m_2655_, v_inst_2656_, v_inst_2657_, v_inst_2658_, v_h_boxed_2661_, v_n_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, uint64_t v_h_2666_, lean_object* v_n_2667_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; 
v___x_2668_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2669_ = lean_box_uint64(v_h_2666_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v_n_2667_);
v___x_2671_ = 2;
v___x_2672_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2663_, v_inst_2665_, v_inst_2664_, v___x_2668_, v___x_2670_, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_h_2676_, lean_object* v_n_2677_){
_start:
{
uint64_t v_h_boxed_2678_; lean_object* v_res_2679_; 
v_h_boxed_2678_ = lean_unbox_uint64(v_h_2676_);
lean_dec_ref(v_h_2676_);
v_res_2679_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_h_boxed_2678_, v_n_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object* v_m_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, uint64_t v_h_2684_, lean_object* v_n_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2681_, v_inst_2682_, v_inst_2683_, v_h_2684_, v_n_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object* v_m_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_h_2691_, lean_object* v_n_2692_){
_start:
{
uint64_t v_h_boxed_2693_; lean_object* v_res_2694_; 
v_h_boxed_2693_ = lean_unbox_uint64(v_h_2691_);
lean_dec_ref(v_h_2691_);
v_res_2694_ = l_Lean_Widget_addPanelWidgetScoped(v_m_2687_, v_inst_2688_, v_inst_2689_, v_inst_2690_, v_h_boxed_2693_, v_n_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t v_x_2695_, uint64_t v_y_2696_){
_start:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_uint64_dec_lt(v_x_2695_, v_y_2696_);
if (v___x_2697_ == 0)
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_uint64_dec_eq(v_x_2695_, v_y_2696_);
if (v___x_2698_ == 0)
{
uint8_t v___x_2699_; 
v___x_2699_ = 2;
return v___x_2699_;
}
else
{
uint8_t v___x_2700_; 
v___x_2700_ = 1;
return v___x_2700_;
}
}
else
{
uint8_t v___x_2701_; 
v___x_2701_ = 0;
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object* v_x_2702_, lean_object* v_y_2703_){
_start:
{
uint64_t v_x_boxed_2704_; uint64_t v_y_boxed_2705_; uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_x_boxed_2704_ = lean_unbox_uint64(v_x_2702_);
lean_dec_ref(v_x_2702_);
v_y_boxed_2705_ = lean_unbox_uint64(v_y_2703_);
lean_dec_ref(v_y_2703_);
v_res_2706_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_boxed_2704_, v_y_boxed_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object* v_wi_2708_, lean_object* v___f_2709_, lean_object* v_s_2710_){
_start:
{
uint64_t v_javascriptHash_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_javascriptHash_2711_ = lean_ctor_get_uint64(v_wi_2708_, sizeof(void*)*2);
v___x_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2712_, 0, v_wi_2708_);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_box_uint64(v_javascriptHash_2711_);
lean_inc(v_s_2710_);
lean_inc_ref(v___f_2709_);
v___x_2715_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___f_2709_, v_s_2710_, v___x_2714_, v___x_2713_);
v___x_2716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2712_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = lean_box_uint64(v_javascriptHash_2711_);
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2709_, v___x_2717_, v___x_2716_, v_s_2710_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object* v___f_2719_, lean_object* v_env_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2722_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2721_, v_env_2720_, v___f_2719_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object* v_inst_2724_, lean_object* v_wi_2725_){
_start:
{
lean_object* v_modifyEnv_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; 
v_modifyEnv_2726_ = lean_ctor_get(v_inst_2724_, 1);
lean_inc(v_modifyEnv_2726_);
lean_dec_ref(v_inst_2724_);
v___f_2727_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___f_2728_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2728_, 0, v_wi_2725_);
lean_closure_set(v___f_2728_, 1, v___f_2727_);
v___f_2729_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2729_, 0, v___f_2728_);
v___x_2730_ = lean_apply_1(v_modifyEnv_2726_, v___f_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object* v_m_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_wi_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Widget_addPanelWidgetLocal___redArg(v_inst_2733_, v_wi_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object* v_m_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_wi_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Widget_addPanelWidgetLocal(v_m_2736_, v_inst_2737_, v_inst_2738_, v_wi_2739_);
lean_dec_ref(v_inst_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object* v___f_2741_, uint64_t v_h_2742_, lean_object* v_st_2743_){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_box_uint64(v_h_2742_);
v___x_2745_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___f_2741_, v___x_2744_, v_st_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object* v___f_2746_, lean_object* v_h_2747_, lean_object* v_st_2748_){
_start:
{
uint64_t v_h_boxed_2749_; lean_object* v_res_2750_; 
v_h_boxed_2749_ = lean_unbox_uint64(v_h_2747_);
lean_dec_ref(v_h_2747_);
v_res_2750_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2746_, v_h_boxed_2749_, v_st_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object* v_inst_2751_, uint64_t v_h_2752_){
_start:
{
lean_object* v_modifyEnv_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; 
v_modifyEnv_2753_ = lean_ctor_get(v_inst_2751_, 1);
lean_inc(v_modifyEnv_2753_);
lean_dec_ref(v_inst_2751_);
v___f_2754_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___x_2755_ = lean_box_uint64(v_h_2752_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2756_, 0, v___f_2754_);
lean_closure_set(v___f_2756_, 1, v___x_2755_);
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2757_, 0, v___f_2756_);
v___x_2758_ = lean_apply_1(v_modifyEnv_2753_, v___f_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object* v_inst_2759_, lean_object* v_h_2760_){
_start:
{
uint64_t v_h_boxed_2761_; lean_object* v_res_2762_; 
v_h_boxed_2761_ = lean_unbox_uint64(v_h_2760_);
lean_dec_ref(v_h_2760_);
v_res_2762_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2759_, v_h_boxed_2761_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget(lean_object* v_m_2763_, lean_object* v_inst_2764_, lean_object* v_inst_2765_, uint64_t v_h_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2765_, v_h_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object* v_m_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_h_2771_){
_start:
{
uint64_t v_h_boxed_2772_; lean_object* v_res_2773_; 
v_h_boxed_2772_ = lean_unbox_uint64(v_h_2771_);
lean_dec_ref(v_h_2771_);
v_res_2773_ = l_Lean_Widget_erasePanelWidget(v_m_2768_, v_inst_2769_, v_inst_2770_, v_h_boxed_2772_);
lean_dec_ref(v_inst_2769_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t v_hash_2774_, lean_object* v_props_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_val_2783_; lean_object* v_env_2786_; lean_object* v___x_2787_; 
v___x_2779_ = lean_st_ref_get(v_a_2777_);
v___x_2780_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_2781_ = lean_st_ref_get(v___x_2780_);
v_env_2786_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_ref(v_env_2786_);
lean_dec(v___x_2779_);
v___x_2787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_2781_, v_hash_2774_);
lean_dec(v___x_2781_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; lean_object* v_toEnvExtension_2789_; lean_object* v_asyncMode_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_2789_ = lean_ctor_get(v___x_2788_, 0);
v_asyncMode_2790_ = lean_ctor_get(v_toEnvExtension_2789_, 2);
v___x_2791_ = lean_box(1);
v___x_2792_ = lean_box(0);
v___x_2793_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2791_, v___x_2788_, v_env_2786_, v_asyncMode_2790_, v___x_2792_);
v___x_2794_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v___x_2793_, v_hash_2774_);
lean_dec(v___x_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
lean_dec_ref(v_props_2775_);
v___x_2795_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_2796_ = lean_uint64_to_nat(v_hash_2774_);
v___x_2797_ = l_Nat_reprFast(v___x_2796_);
v___x_2798_ = lean_string_append(v___x_2795_, v___x_2797_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_2800_ = lean_string_append(v___x_2798_, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
v___x_2802_ = l_Lean_MessageData_ofFormat(v___x_2801_);
v___x_2803_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__0___redArg(v___x_2802_, v_a_2776_, v_a_2777_);
return v___x_2803_;
}
else
{
lean_object* v_val_2804_; lean_object* v_fst_2805_; 
v_val_2804_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v___x_2794_, 1);
v_fst_2805_ = lean_ctor_get(v_val_2804_, 0);
lean_inc(v_fst_2805_);
lean_dec(v_val_2804_);
v_val_2783_ = v_fst_2805_;
goto v___jp_2782_;
}
}
else
{
lean_object* v_val_2806_; lean_object* v_fst_2807_; 
lean_dec_ref(v_env_2786_);
v_val_2806_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v___x_2787_, 1);
v_fst_2807_ = lean_ctor_get(v_val_2806_, 0);
lean_inc(v_fst_2807_);
lean_dec(v_val_2806_);
v_val_2783_ = v_fst_2807_;
goto v___jp_2782_;
}
v___jp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2784_, 0, v_val_2783_);
lean_ctor_set(v___x_2784_, 1, v_props_2775_);
lean_ctor_set_uint64(v___x_2784_, sizeof(void*)*2, v_hash_2774_);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object* v_hash_2808_, lean_object* v_props_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
uint64_t v_hash_boxed_2813_; lean_object* v_res_2814_; 
v_hash_boxed_2813_ = lean_unbox_uint64(v_hash_2808_);
lean_dec_ref(v_hash_2808_);
v_res_2814_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_boxed_2813_, v_props_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object* v_t_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; lean_object* v_infoState_2819_; uint8_t v_enabled_2820_; 
v___x_2818_ = lean_st_ref_get(v___y_2816_);
v_infoState_2819_ = lean_ctor_get(v___x_2818_, 7);
lean_inc_ref(v_infoState_2819_);
lean_dec(v___x_2818_);
v_enabled_2820_ = lean_ctor_get_uint8(v_infoState_2819_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2819_);
if (v_enabled_2820_ == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec_ref(v_t_2815_);
v___x_2821_ = lean_box(0);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; lean_object* v_infoState_2824_; lean_object* v_env_2825_; lean_object* v_nextMacroScope_2826_; lean_object* v_ngen_2827_; lean_object* v_auxDeclNGen_2828_; lean_object* v_traceState_2829_; lean_object* v_cache_2830_; lean_object* v_messages_2831_; lean_object* v_snapshotTasks_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2854_; 
v___x_2823_ = lean_st_ref_take(v___y_2816_);
v_infoState_2824_ = lean_ctor_get(v___x_2823_, 7);
v_env_2825_ = lean_ctor_get(v___x_2823_, 0);
v_nextMacroScope_2826_ = lean_ctor_get(v___x_2823_, 1);
v_ngen_2827_ = lean_ctor_get(v___x_2823_, 2);
v_auxDeclNGen_2828_ = lean_ctor_get(v___x_2823_, 3);
v_traceState_2829_ = lean_ctor_get(v___x_2823_, 4);
v_cache_2830_ = lean_ctor_get(v___x_2823_, 5);
v_messages_2831_ = lean_ctor_get(v___x_2823_, 6);
v_snapshotTasks_2832_ = lean_ctor_get(v___x_2823_, 8);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2834_ = v___x_2823_;
v_isShared_2835_ = v_isSharedCheck_2854_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_snapshotTasks_2832_);
lean_inc(v_infoState_2824_);
lean_inc(v_messages_2831_);
lean_inc(v_cache_2830_);
lean_inc(v_traceState_2829_);
lean_inc(v_auxDeclNGen_2828_);
lean_inc(v_ngen_2827_);
lean_inc(v_nextMacroScope_2826_);
lean_inc(v_env_2825_);
lean_dec(v___x_2823_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2854_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
uint8_t v_enabled_2836_; lean_object* v_assignment_2837_; lean_object* v_lazyAssignment_2838_; lean_object* v_trees_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2853_; 
v_enabled_2836_ = lean_ctor_get_uint8(v_infoState_2824_, sizeof(void*)*3);
v_assignment_2837_ = lean_ctor_get(v_infoState_2824_, 0);
v_lazyAssignment_2838_ = lean_ctor_get(v_infoState_2824_, 1);
v_trees_2839_ = lean_ctor_get(v_infoState_2824_, 2);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_infoState_2824_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2841_ = v_infoState_2824_;
v_isShared_2842_ = v_isSharedCheck_2853_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_trees_2839_);
lean_inc(v_lazyAssignment_2838_);
lean_inc(v_assignment_2837_);
lean_dec(v_infoState_2824_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2853_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = l_Lean_PersistentArray_push___redArg(v_trees_2839_, v_t_2815_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 2, v___x_2843_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_assignment_2837_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_lazyAssignment_2838_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v___x_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*3, v_enabled_2836_);
v___x_2845_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 7, v___x_2845_);
v___x_2847_ = v___x_2834_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_env_2825_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_nextMacroScope_2826_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_ngen_2827_);
lean_ctor_set(v_reuseFailAlloc_2851_, 3, v_auxDeclNGen_2828_);
lean_ctor_set(v_reuseFailAlloc_2851_, 4, v_traceState_2829_);
lean_ctor_set(v_reuseFailAlloc_2851_, 5, v_cache_2830_);
lean_ctor_set(v_reuseFailAlloc_2851_, 6, v_messages_2831_);
lean_ctor_set(v_reuseFailAlloc_2851_, 7, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2851_, 8, v_snapshotTasks_2832_);
v___x_2847_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_st_ref_set(v___y_2816_, v___x_2847_);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2855_, v___y_2856_);
lean_dec(v___y_2856_);
return v_res_2858_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_unsigned_to_nat(32u);
v___x_2860_ = lean_mk_empty_array_with_capacity(v___x_2859_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2862_ = ((size_t)5ULL);
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = lean_unsigned_to_nat(32u);
v___x_2865_ = lean_mk_empty_array_with_capacity(v___x_2864_);
v___x_2866_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0);
v___x_2867_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v___x_2865_);
lean_ctor_set(v___x_2867_, 2, v___x_2863_);
lean_ctor_set(v___x_2867_, 3, v___x_2863_);
lean_ctor_set_usize(v___x_2867_, 4, v___x_2862_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object* v_t_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; lean_object* v_infoState_2873_; uint8_t v_enabled_2874_; 
v___x_2872_ = lean_st_ref_get(v___y_2870_);
v_infoState_2873_ = lean_ctor_get(v___x_2872_, 7);
lean_inc_ref(v_infoState_2873_);
lean_dec(v___x_2872_);
v_enabled_2874_ = lean_ctor_get_uint8(v_infoState_2873_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2873_);
if (v_enabled_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v_t_2868_);
v___x_2875_ = lean_box(0);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1);
v___x_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2878_, 0, v_t_2868_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v___x_2878_, v___y_2870_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object* v_t_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t v_hash_2885_, lean_object* v_props_2886_, lean_object* v_stx_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2885_, v_props_2886_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_a_2892_);
lean_ctor_set(v___x_2893_, 1, v_stx_2887_);
v___x_2894_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
v___x_2895_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v___x_2894_, v_a_2888_, v_a_2889_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_stx_2887_);
v_a_2896_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2891_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2891_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object* v_hash_2904_, lean_object* v_props_2905_, lean_object* v_stx_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
uint64_t v_hash_boxed_2910_; lean_object* v_res_2911_; 
v_hash_boxed_2910_ = lean_unbox_uint64(v_hash_2904_);
lean_dec_ref(v_hash_2904_);
v_res_2911_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_boxed_2910_, v_props_2905_, v_stx_2906_, v_a_2907_, v_a_2908_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object* v_t_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2912_, v___y_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object* v_t_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object* v_x_2928_){
_start:
{
lean_object* v_name_2929_; lean_object* v_javascript_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2950_; 
v_name_2929_ = lean_ctor_get(v_x_2928_, 0);
v_javascript_2930_ = lean_ctor_get(v_x_2928_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_x_2928_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2932_ = v_x_2928_;
v_isShared_2933_ = v_isSharedCheck_2950_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_javascript_2930_);
lean_inc(v_name_2929_);
lean_dec(v_x_2928_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2950_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2934_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_2935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_name_2929_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 1, v___x_2935_);
lean_ctor_set(v___x_2932_, 0, v___x_2934_);
v___x_2937_ = v___x_2932_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_2941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_javascript_2930_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___x_2938_);
v___x_2944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_ctor_set(v___x_2944_, 1, v___x_2938_);
v___x_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2939_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_2947_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_2945_, v___x_2946_);
v___x_2948_ = l_Lean_Json_mkObj(v___x_2947_);
lean_dec(v___x_2947_);
return v___x_2948_;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = 1;
v___x_2959_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_2960_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2959_, v___x_2958_);
return v___x_2960_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1___closed__3_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_));
v___x_2962_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2);
v___x_2963_ = lean_string_append(v___x_2962_, v___x_2961_);
return v___x_2963_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = 1;
v___x_2967_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4));
v___x_2968_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2967_, v___x_2966_);
return v___x_2968_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5);
v___x_2970_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2971_ = lean_string_append(v___x_2970_, v___x_2969_);
return v___x_2971_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2973_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6);
v___x_2974_ = lean_string_append(v___x_2973_, v___x_2972_);
return v___x_2974_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = 1;
v___x_2978_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8));
v___x_2979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2978_, v___x_2977_);
return v___x_2979_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9);
v___x_2981_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2982_ = lean_string_append(v___x_2981_, v___x_2980_);
return v___x_2982_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2984_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10);
v___x_2985_ = lean_string_append(v___x_2984_, v___x_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object* v_json_2986_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
lean_inc(v_json_2986_);
v___x_2988_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_2986_, v___x_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_json_2986_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2993_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7);
v___x_2994_ = lean_string_append(v___x_2993_, v_a_2989_);
lean_dec(v_a_2989_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2994_);
v___x_2996_ = v___x_2991_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_json_2986_);
v_a_2999_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2988_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2988_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 0);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_2988_, 1);
v___x_3008_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_3009_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_2986_, v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3019_; 
lean_dec(v_a_3007_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3014_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11);
v___x_3015_ = lean_string_append(v___x_3014_, v_a_3010_);
lean_dec(v_a_3010_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3015_);
v___x_3017_ = v___x_3012_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
else
{
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_a_3007_);
v_a_3020_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3009_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3009_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set_tag(v___x_3022_, 0);
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_a_3028_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3030_ = v___x_3009_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3009_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v_a_3007_);
lean_ctor_set(v___x_3032_, 1, v_a_3028_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object* v_uwd_3039_){
_start:
{
lean_object* v_javascript_3040_; uint64_t v___x_3041_; lean_object* v___x_3042_; 
v_javascript_3040_ = lean_ctor_get(v_uwd_3039_, 1);
v___x_3041_ = lean_string_hash(v_javascript_3040_);
lean_inc_ref(v_javascript_3040_);
v___x_3042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3042_, 0, v_javascript_3040_);
lean_ctor_set_uint64(v___x_3042_, sizeof(void*)*1, v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object* v_uwd_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(v_uwd_3043_);
lean_dec_ref(v_uwd_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object* v_____do__lift_3047_, lean_object* v_id_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v___x_3051_, lean_object* v_____do__lift_3052_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3054_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_3047_, v_____do__lift_3052_, v___x_3053_, v_id_3048_);
v___x_3055_ = l_Lean_ofExcept___redArg(v_inst_3049_, v_inst_3050_, v___x_3051_, v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object* v_____do__lift_3056_, lean_object* v_id_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v___x_3060_, lean_object* v_____do__lift_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(v_____do__lift_3056_, v_id_3057_, v_inst_3058_, v_inst_3059_, v___x_3060_, v_____do__lift_3061_);
lean_dec_ref(v_____do__lift_3061_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object* v_id_3063_, lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v___x_3066_, lean_object* v_toBind_3067_, lean_object* v_inst_3068_, lean_object* v_____do__lift_3069_){
_start:
{
lean_object* v___f_3070_; lean_object* v___x_3071_; 
v___f_3070_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_3070_, 0, v_____do__lift_3069_);
lean_closure_set(v___f_3070_, 1, v_id_3063_);
lean_closure_set(v___f_3070_, 2, v_inst_3064_);
lean_closure_set(v___f_3070_, 3, v_inst_3065_);
lean_closure_set(v___f_3070_, 4, v___x_3066_);
v___x_3071_ = lean_apply_4(v_toBind_3067_, lean_box(0), lean_box(0), v_inst_3068_, v___f_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_id_3077_){
_start:
{
lean_object* v_toBind_3078_; lean_object* v_getEnv_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; 
v_toBind_3078_ = lean_ctor_get(v_inst_3073_, 1);
lean_inc_n(v_toBind_3078_, 2);
v_getEnv_3079_ = lean_ctor_get(v_inst_3074_, 0);
lean_inc(v_getEnv_3079_);
lean_dec_ref(v_inst_3074_);
v___x_3080_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0));
v___f_3081_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3081_, 0, v_id_3077_);
lean_closure_set(v___f_3081_, 1, v_inst_3073_);
lean_closure_set(v___f_3081_, 2, v_inst_3076_);
lean_closure_set(v___f_3081_, 3, v___x_3080_);
lean_closure_set(v___f_3081_, 4, v_toBind_3078_);
lean_closure_set(v___f_3081_, 5, v_inst_3075_);
v___x_3082_ = lean_apply_4(v_toBind_3078_, lean_box(0), lean_box(0), v_getEnv_3079_, v___f_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object* v_m_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_id_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(v_inst_3084_, v_inst_3085_, v_inst_3086_, v_inst_3087_, v_id_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object* v_text_3090_, lean_object* v_hoverLine_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3093_) == 9)
{
lean_object* v_i_3095_; lean_object* v___x_3096_; 
v_i_3095_ = lean_ctor_get(v_x_3093_, 0);
v___x_3096_ = l_Lean_Elab_Info_pos_x3f(v_x_3093_);
if (lean_obj_tag(v___x_3096_) == 1)
{
lean_object* v_val_3097_; lean_object* v___x_3098_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_Elab_Info_tailPos_x3f(v_x_3093_);
if (lean_obj_tag(v___x_3098_) == 1)
{
lean_object* v_val_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3114_; 
v_val_3099_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3101_ = v___x_3098_;
v_isShared_3102_ = v_isSharedCheck_3114_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_val_3099_);
lean_dec(v___x_3098_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3114_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v_line_3104_; uint8_t v___x_3105_; 
lean_inc_ref(v_text_3090_);
v___x_3103_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3090_, v_val_3097_);
lean_dec(v_val_3097_);
v_line_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_line_3104_);
lean_dec_ref(v___x_3103_);
v___x_3105_ = lean_nat_dec_le(v_line_3104_, v_hoverLine_3091_);
lean_dec(v_line_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; 
lean_del_object(v___x_3101_);
lean_dec(v_val_3099_);
lean_dec_ref(v_text_3090_);
v___x_3106_ = lean_box(0);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; lean_object* v_line_3108_; uint8_t v___x_3109_; 
v___x_3107_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3090_, v_val_3099_);
lean_dec(v_val_3099_);
v_line_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_line_3108_);
lean_dec_ref(v___x_3107_);
v___x_3109_ = lean_nat_dec_le(v_hoverLine_3091_, v_line_3108_);
lean_dec(v_line_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; 
lean_del_object(v___x_3101_);
v___x_3110_ = lean_box(0);
return v___x_3110_;
}
else
{
lean_object* v___x_3112_; 
lean_inc_ref(v_i_3095_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v_i_3095_);
v___x_3112_ = v___x_3101_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_i_3095_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
else
{
lean_object* v___x_3115_; 
lean_dec(v___x_3098_);
lean_dec(v_val_3097_);
lean_dec_ref(v_text_3090_);
v___x_3115_ = lean_box(0);
return v___x_3115_;
}
}
else
{
lean_object* v___x_3116_; 
lean_dec(v___x_3096_);
lean_dec_ref(v_text_3090_);
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
}
else
{
lean_object* v___x_3117_; 
lean_dec_ref(v_text_3090_);
v___x_3117_ = lean_box(0);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object* v_text_3118_, lean_object* v_hoverLine_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v_x_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Widget_widgetInfosAt_x3f___lam__0(v_text_3118_, v_hoverLine_3119_, v_x_3120_, v_x_3121_, v_x_3122_);
lean_dec_ref(v_x_3122_);
lean_dec_ref(v_x_3121_);
lean_dec_ref(v_x_3120_);
lean_dec(v_hoverLine_3119_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object* v_text_3124_, lean_object* v_t_3125_, lean_object* v_hoverLine_3126_){
_start:
{
lean_object* v___f_3127_; lean_object* v___x_3128_; 
v___f_3127_ = lean_alloc_closure((void*)(l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_3127_, 0, v_text_3124_);
lean_closure_set(v___f_3127_, 1, v_hoverLine_3126_);
v___x_3128_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3127_, v_t_3125_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object* v_j_3129_, lean_object* v_k_3130_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = l_Lean_Json_getObjValD(v_j_3129_, v_k_3130_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object* v_j_3133_, lean_object* v_k_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_j_3133_, v_k_3134_);
lean_dec_ref(v_k_3134_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object* v_x_3138_){
_start:
{
if (lean_obj_tag(v_x_3138_) == 0)
{
lean_object* v___x_3139_; 
v___x_3139_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0));
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_x_3138_);
v___x_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object* v_j_3142_, lean_object* v_k_3143_){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = l_Lean_Json_getObjValD(v_j_3142_, v_k_3143_);
v___x_3145_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object* v_j_3146_, lean_object* v_k_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_j_3146_, v_k_3147_);
lean_dec_ref(v_k_3147_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object* v_json_3153_){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v_a_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v_a_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3176_; 
v___x_3154_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc_n(v_json_3153_, 4);
v___x_3155_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3153_, v___x_3154_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref(v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3158_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3153_, v___x_3157_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref(v___x_3158_);
v___x_3160_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3161_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3153_, v___x_3160_);
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref(v___x_3161_);
v___x_3163_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3164_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3153_, v___x_3163_);
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3167_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3153_, v___x_3166_);
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3172_, 0, v_a_3156_);
lean_ctor_set(v___x_3172_, 1, v_a_3159_);
lean_ctor_set(v___x_3172_, 2, v_a_3162_);
lean_ctor_set(v___x_3172_, 3, v_a_3165_);
lean_ctor_set(v___x_3172_, 4, v_a_3168_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3172_);
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(lean_object* v_k_3179_, lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 0)
{
lean_object* v___x_3181_; 
lean_dec_ref(v_k_3179_);
v___x_3181_ = lean_box(0);
return v___x_3181_;
}
else
{
lean_object* v_val_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_val_3182_ = lean_ctor_get(v_x_3180_, 0);
lean_inc(v_val_3182_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_k_3179_);
lean_ctor_set(v___x_3183_, 1, v_val_3182_);
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0___boxed(lean_object* v_k_3186_, lean_object* v_x_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v_k_3186_, v_x_3187_);
lean_dec(v_x_3187_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(lean_object* v_x_3189_){
_start:
{
lean_object* v_id_3190_; lean_object* v_javascriptHash_3191_; lean_object* v_props_3192_; lean_object* v_range_x3f_3193_; lean_object* v_name_x3f_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_id_3190_ = lean_ctor_get(v_x_3189_, 0);
v_javascriptHash_3191_ = lean_ctor_get(v_x_3189_, 1);
v_props_3192_ = lean_ctor_get(v_x_3189_, 2);
v_range_x3f_3193_ = lean_ctor_get(v_x_3189_, 3);
v_name_x3f_3194_ = lean_ctor_get(v_x_3189_, 4);
v___x_3195_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_id_3190_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v_id_3190_);
v___x_3197_ = lean_box(0);
v___x_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_javascriptHash_3191_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v_javascriptHash_3191_);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v___x_3197_);
v___x_3202_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_props_3192_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v_props_3192_);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3197_);
v___x_3205_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3206_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v___x_3205_, v_range_x3f_3193_);
v___x_3207_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3208_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38__spec__0(v___x_3207_, v_name_x3f_3194_);
v___x_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3197_);
v___x_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3206_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3204_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3201_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3198_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3215_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3213_, v___x_3214_);
v___x_3216_ = l_Lean_Json_mkObj(v___x_3215_);
lean_dec(v___x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38____boxed(lean_object* v_x_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(v_x_3217_);
lean_dec_ref(v_x_3217_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v_toWidgetInstance_3223_; lean_object* v_range_x3f_3224_; lean_object* v_name_x3f_3225_; lean_object* v_id_3226_; uint64_t v_javascriptHash_3227_; lean_object* v_props_3228_; lean_object* v___x_3229_; lean_object* v_fst_3230_; lean_object* v_snd_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3271_; 
v_toWidgetInstance_3223_ = lean_ctor_get(v_a_3221_, 0);
lean_inc_ref(v_toWidgetInstance_3223_);
v_range_x3f_3224_ = lean_ctor_get(v_a_3221_, 1);
lean_inc(v_range_x3f_3224_);
v_name_x3f_3225_ = lean_ctor_get(v_a_3221_, 2);
lean_inc(v_name_x3f_3225_);
lean_dec_ref(v_a_3221_);
v_id_3226_ = lean_ctor_get(v_toWidgetInstance_3223_, 0);
lean_inc(v_id_3226_);
v_javascriptHash_3227_ = lean_ctor_get_uint64(v_toWidgetInstance_3223_, sizeof(void*)*2);
v_props_3228_ = lean_ctor_get(v_toWidgetInstance_3223_, 1);
lean_inc_ref(v_props_3228_);
lean_dec_ref(v_toWidgetInstance_3223_);
v___x_3229_ = lean_apply_1(v_props_3228_, v_a_3222_);
v_fst_3230_ = lean_ctor_get(v___x_3229_, 0);
v_snd_3231_ = lean_ctor_get(v___x_3229_, 1);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3233_ = v___x_3229_;
v_isShared_3234_ = v_isSharedCheck_3271_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_snd_3231_);
lean_inc(v_fst_3230_);
lean_dec(v___x_3229_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3271_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___y_3241_; lean_object* v_fst_3242_; lean_object* v_snd_3243_; lean_object* v_fst_3250_; 
v___x_3235_ = 1;
v___x_3236_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3226_, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
v___x_3238_ = lean_uint64_to_nat(v_javascriptHash_3227_);
v___x_3239_ = l_Lean_bignumToJson(v___x_3238_);
if (lean_obj_tag(v_range_x3f_3224_) == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_box(0);
v_fst_3250_ = v___x_3261_;
goto v___jp_3249_;
}
else
{
lean_object* v_val_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3270_; 
v_val_3262_ = lean_ctor_get(v_range_x3f_3224_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_range_x3f_3224_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3264_ = v_range_x3f_3224_;
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_val_3262_);
lean_dec(v_range_x3f_3224_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_3262_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
v_fst_3250_ = v___x_3268_;
goto v___jp_3249_;
}
}
}
v___jp_3240_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3237_);
lean_ctor_set(v___x_3244_, 1, v___x_3239_);
lean_ctor_set(v___x_3244_, 2, v_fst_3230_);
lean_ctor_set(v___x_3244_, 3, v___y_3241_);
lean_ctor_set(v___x_3244_, 4, v_fst_3242_);
v___x_3245_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_38_(v___x_3244_);
lean_dec_ref_known(v___x_3244_, 5);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v_snd_3243_);
lean_ctor_set(v___x_3233_, 0, v___x_3245_);
v___x_3247_ = v___x_3233_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_snd_3243_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
v___jp_3249_:
{
if (lean_obj_tag(v_name_x3f_3225_) == 0)
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_box(0);
v___y_3241_ = v_fst_3250_;
v_fst_3242_ = v___x_3251_;
v_snd_3243_ = v_snd_3231_;
goto v___jp_3240_;
}
else
{
lean_object* v_val_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3260_; 
v_val_3252_ = lean_ctor_get(v_name_x3f_3225_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_name_x3f_3225_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3254_ = v_name_x3f_3225_;
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_val_3252_);
lean_dec(v_name_x3f_3225_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_val_3252_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3256_);
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
v___y_3241_ = v_fst_3250_;
v_fst_3242_ = v___x_3258_;
v_snd_3243_ = v_snd_3231_;
goto v___jp_3240_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_props_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_props_3272_);
lean_ctor_set(v___x_3274_, 1, v___y_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(v_j_3275_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v_id_3286_; lean_object* v_javascriptHash_3287_; lean_object* v_props_3288_; lean_object* v_range_x3f_3289_; lean_object* v_name_x3f_3290_; lean_object* v___x_3291_; 
v_a_3285_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3276_, 1);
v_id_3286_ = lean_ctor_get(v_a_3285_, 0);
lean_inc(v_id_3286_);
v_javascriptHash_3287_ = lean_ctor_get(v_a_3285_, 1);
lean_inc(v_javascriptHash_3287_);
v_props_3288_ = lean_ctor_get(v_a_3285_, 2);
lean_inc(v_props_3288_);
v_range_x3f_3289_ = lean_ctor_get(v_a_3285_, 3);
lean_inc(v_range_x3f_3289_);
v_name_x3f_3290_ = lean_ctor_get(v_a_3285_, 4);
lean_inc(v_name_x3f_3290_);
lean_dec(v_a_3285_);
v___x_3291_ = l_Lean_Name_fromJson_x3f(v_id_3286_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec(v_name_x3f_3290_);
lean_dec(v_range_x3f_3289_);
lean_dec(v_props_3288_);
lean_dec(v_javascriptHash_3287_);
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
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3301_ = l_Lean_UInt64_fromJson_x3f(v_javascriptHash_3287_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_a_3300_);
lean_dec(v_name_x3f_3290_);
lean_dec(v_range_x3f_3289_);
lean_dec(v_props_3288_);
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3364_; 
v_a_3310_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3312_ = v___x_3301_;
v_isShared_3313_ = v_isSharedCheck_3364_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3301_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3364_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___f_3314_; lean_object* v___y_3316_; lean_object* v_____do__lift_3317_; lean_object* v_____do__lift_3325_; 
v___f_3314_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_), 2, 1);
lean_closure_set(v___f_3314_, 0, v_props_3288_);
if (lean_obj_tag(v_range_x3f_3289_) == 0)
{
lean_object* v___x_3345_; 
v___x_3345_ = lean_box(0);
v_____do__lift_3325_ = v___x_3345_;
goto v___jp_3324_;
}
else
{
lean_object* v_val_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3363_; 
v_val_3346_ = lean_ctor_get(v_range_x3f_3289_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_range_x3f_3289_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3348_ = v_range_x3f_3289_;
v_isShared_3349_ = v_isSharedCheck_3363_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_val_3346_);
lean_dec(v_range_x3f_3289_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3363_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_3346_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_del_object(v___x_3348_);
lean_dec_ref(v___f_3314_);
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3300_);
lean_dec(v_name_x3f_3290_);
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; 
v_a_3359_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3350_, 1);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_a_3359_);
v___x_3361_ = v___x_3348_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
v_____do__lift_3325_ = v___x_3361_;
goto v___jp_3324_;
}
}
}
}
v___jp_3315_:
{
lean_object* v___x_3318_; uint64_t v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3318_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3318_, 0, v_a_3300_);
lean_ctor_set(v___x_3318_, 1, v___f_3314_);
v___x_3319_ = lean_unbox_uint64(v_a_3310_);
lean_dec(v_a_3310_);
lean_ctor_set_uint64(v___x_3318_, sizeof(void*)*2, v___x_3319_);
v___x_3320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___y_3316_);
lean_ctor_set(v___x_3320_, 2, v_____do__lift_3317_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3320_);
v___x_3322_ = v___x_3312_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
v___jp_3324_:
{
if (lean_obj_tag(v_name_x3f_3290_) == 0)
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_box(0);
v___y_3316_ = v_____do__lift_3325_;
v_____do__lift_3317_ = v___x_3326_;
goto v___jp_3315_;
}
else
{
lean_object* v_val_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3344_; 
v_val_3327_ = lean_ctor_get(v_name_x3f_3290_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_name_x3f_3290_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3329_ = v_name_x3f_3290_;
v_isShared_3330_ = v_isSharedCheck_3344_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_val_3327_);
lean_dec(v_name_x3f_3290_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3344_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_Json_getStr_x3f(v_val_3327_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_del_object(v___x_3329_);
lean_dec(v_____do__lift_3325_);
lean_dec_ref(v___f_3314_);
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3300_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; 
v_a_3340_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3331_, 1);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v_a_3340_);
v___x_3342_ = v___x_3329_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
v___y_3316_ = v_____do__lift_3325_;
v_____do__lift_3317_ = v___x_3342_;
goto v___jp_3315_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object* v_j_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3368_, v_a_3369_);
lean_dec_ref(v_a_3369_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object* v_json_3378_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v___x_3379_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3380_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3378_, v___x_3379_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(lean_object* v_x_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3392_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v_x_3391_);
v___x_3394_ = lean_box(0);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3394_);
v___x_3397_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3398_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3396_, v___x_3397_);
v___x_3399_ = l_Lean_Json_mkObj(v___x_3398_);
lean_dec(v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t v_sz_3402_, size_t v_i_3403_, lean_object* v_bs_3404_){
_start:
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_usize_dec_lt(v_i_3403_, v_sz_3402_);
if (v___x_3405_ == 0)
{
return v_bs_3404_;
}
else
{
lean_object* v_v_3406_; lean_object* v___x_3407_; lean_object* v_bs_x27_3408_; size_t v___x_3409_; size_t v___x_3410_; lean_object* v___x_3411_; 
v_v_3406_ = lean_array_uget(v_bs_3404_, v_i_3403_);
v___x_3407_ = lean_unsigned_to_nat(0u);
v_bs_x27_3408_ = lean_array_uset(v_bs_3404_, v_i_3403_, v___x_3407_);
v___x_3409_ = ((size_t)1ULL);
v___x_3410_ = lean_usize_add(v_i_3403_, v___x_3409_);
v___x_3411_ = lean_array_uset(v_bs_x27_3408_, v_i_3403_, v_v_3406_);
v_i_3403_ = v___x_3410_;
v_bs_3404_ = v___x_3411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object* v_sz_3413_, lean_object* v_i_3414_, lean_object* v_bs_3415_){
_start:
{
size_t v_sz_boxed_3416_; size_t v_i_boxed_3417_; lean_object* v_res_3418_; 
v_sz_boxed_3416_ = lean_unbox_usize(v_sz_3413_);
lean_dec(v_sz_3413_);
v_i_boxed_3417_ = lean_unbox_usize(v_i_3414_);
lean_dec(v_i_3414_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_boxed_3416_, v_i_boxed_3417_, v_bs_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object* v_a_3419_){
_start:
{
size_t v_sz_3420_; size_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_sz_3420_ = lean_array_size(v_a_3419_);
v___x_3421_ = ((size_t)0ULL);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3420_, v___x_3421_, v_a_3419_);
v___x_3423_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t v_sz_3424_, size_t v_i_3425_, lean_object* v_bs_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_usize_dec_lt(v_i_3425_, v_sz_3424_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v_bs_3426_);
lean_ctor_set(v___x_3429_, 1, v___y_3427_);
return v___x_3429_;
}
else
{
lean_object* v_v_3430_; lean_object* v___x_3431_; lean_object* v_fst_3432_; lean_object* v_snd_3433_; lean_object* v___x_3434_; lean_object* v_bs_x27_3435_; size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v_v_3430_ = lean_array_uget_borrowed(v_bs_3426_, v_i_3425_);
lean_inc(v_v_3430_);
v___x_3431_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3430_, v___y_3427_);
v_fst_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_fst_3432_);
v_snd_3433_ = lean_ctor_get(v___x_3431_, 1);
lean_inc(v_snd_3433_);
lean_dec_ref(v___x_3431_);
v___x_3434_ = lean_unsigned_to_nat(0u);
v_bs_x27_3435_ = lean_array_uset(v_bs_3426_, v_i_3425_, v___x_3434_);
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3425_, v___x_3436_);
v___x_3438_ = lean_array_uset(v_bs_x27_3435_, v_i_3425_, v_fst_3432_);
v_i_3425_ = v___x_3437_;
v_bs_3426_ = v___x_3438_;
v___y_3427_ = v_snd_3433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object* v_sz_3440_, lean_object* v_i_3441_, lean_object* v_bs_3442_, lean_object* v___y_3443_){
_start:
{
size_t v_sz_boxed_3444_; size_t v_i_boxed_3445_; lean_object* v_res_3446_; 
v_sz_boxed_3444_ = lean_unbox_usize(v_sz_3440_);
lean_dec(v_sz_3440_);
v_i_boxed_3445_ = lean_unbox_usize(v_i_3441_);
lean_dec(v_i_3441_);
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_boxed_3444_, v_i_boxed_3445_, v_bs_3442_, v___y_3443_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
size_t v_sz_3449_; size_t v___x_3450_; lean_object* v___x_3451_; lean_object* v_fst_3452_; lean_object* v_snd_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3462_; 
v_sz_3449_ = lean_array_size(v_a_3447_);
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3449_, v___x_3450_, v_a_3447_, v_a_3448_);
v_fst_3452_ = lean_ctor_get(v___x_3451_, 0);
v_snd_3453_ = lean_ctor_get(v___x_3451_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3455_ = v___x_3451_;
v_isShared_3456_ = v_isSharedCheck_3462_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snd_3453_);
lean_inc(v_fst_3452_);
lean_dec(v___x_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3462_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3457_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_fst_3452_);
v___x_3458_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_28_(v___x_3457_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3458_);
v___x_3460_ = v___x_3455_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_snd_3453_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t v_sz_3463_, size_t v_i_3464_, lean_object* v_bs_3465_){
_start:
{
uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_lt(v_i_3464_, v_sz_3463_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_bs_3465_);
return v___x_3467_;
}
else
{
lean_object* v_v_3468_; lean_object* v___x_3469_; 
v_v_3468_ = lean_array_uget_borrowed(v_bs_3465_, v_i_3464_);
lean_inc(v_v_3468_);
v___x_3469_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3468_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v_bs_3465_);
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3479_; lean_object* v_bs_x27_3480_; size_t v___x_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
v_a_3478_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3479_ = lean_unsigned_to_nat(0u);
v_bs_x27_3480_ = lean_array_uset(v_bs_3465_, v_i_3464_, v___x_3479_);
v___x_3481_ = ((size_t)1ULL);
v___x_3482_ = lean_usize_add(v_i_3464_, v___x_3481_);
v___x_3483_ = lean_array_uset(v_bs_x27_3480_, v_i_3464_, v_a_3478_);
v_i_3464_ = v___x_3482_;
v_bs_3465_ = v___x_3483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object* v_sz_3485_, lean_object* v_i_3486_, lean_object* v_bs_3487_){
_start:
{
size_t v_sz_boxed_3488_; size_t v_i_boxed_3489_; lean_object* v_res_3490_; 
v_sz_boxed_3488_ = lean_unbox_usize(v_sz_3485_);
lean_dec(v_sz_3485_);
v_i_boxed_3489_ = lean_unbox_usize(v_i_3486_);
lean_dec(v_i_3486_);
v_res_3490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_boxed_3488_, v_i_boxed_3489_, v_bs_3487_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t v_sz_3491_, size_t v_i_3492_, lean_object* v_bs_3493_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_lt(v_i_3492_, v_sz_3491_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_bs_3493_);
return v___x_3495_;
}
else
{
lean_object* v_v_3496_; lean_object* v___x_3497_; lean_object* v_bs_x27_3498_; size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v_v_3496_ = lean_array_uget(v_bs_3493_, v_i_3492_);
v___x_3497_ = lean_unsigned_to_nat(0u);
v_bs_x27_3498_ = lean_array_uset(v_bs_3493_, v_i_3492_, v___x_3497_);
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3492_, v___x_3499_);
v___x_3501_ = lean_array_uset(v_bs_x27_3498_, v_i_3492_, v_v_3496_);
v_i_3492_ = v___x_3500_;
v_bs_3493_ = v___x_3501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_sz_3503_, lean_object* v_i_3504_, lean_object* v_bs_3505_){
_start:
{
size_t v_sz_boxed_3506_; size_t v_i_boxed_3507_; lean_object* v_res_3508_; 
v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3503_);
lean_dec(v_sz_3503_);
v_i_boxed_3507_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_3506_, v_i_boxed_3507_, v_bs_3505_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 4)
{
lean_object* v_elems_3511_; size_t v_sz_3512_; size_t v___x_3513_; lean_object* v___x_3514_; 
v_elems_3511_ = lean_ctor_get(v_x_3510_, 0);
lean_inc_ref(v_elems_3511_);
lean_dec_ref_known(v_x_3510_, 1);
v_sz_3512_ = lean_array_size(v_elems_3511_);
v___x_3513_ = ((size_t)0ULL);
v___x_3514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3512_, v___x_3513_, v_elems_3511_);
return v___x_3514_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3515_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0));
v___x_3516_ = lean_unsigned_to_nat(80u);
v___x_3517_ = l_Lean_Json_pretty(v_x_3510_, v___x_3516_);
v___x_3518_ = lean_string_append(v___x_3515_, v___x_3517_);
lean_dec_ref(v___x_3517_);
v___x_3519_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v___x_3520_ = lean_string_append(v___x_3518_, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_j_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(v_j_3522_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3534_; 
v_a_3533_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3534_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_a_3533_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3543_; size_t v_sz_3544_; size_t v___x_3545_; lean_object* v___x_3546_; 
v_a_3543_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3534_, 1);
v_sz_3544_ = lean_array_size(v_a_3543_);
v___x_3545_ = ((size_t)0ULL);
v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3544_, v___x_3545_, v_a_3543_);
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
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_a_3555_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3546_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3546_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object* v_j_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_j_3563_, v_a_3564_);
lean_dec_ref(v_a_3564_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_bs_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3566_, v_i_3567_, v_bs_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object* v_sz_3571_, lean_object* v_i_3572_, lean_object* v_bs_3573_, lean_object* v___y_3574_){
_start:
{
size_t v_sz_boxed_3575_; size_t v_i_boxed_3576_; lean_object* v_res_3577_; 
v_sz_boxed_3575_ = lean_unbox_usize(v_sz_3571_);
lean_dec(v_sz_3571_);
v_i_boxed_3576_ = lean_unbox_usize(v_i_3572_);
lean_dec(v_i_3572_);
v_res_3577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_boxed_3575_, v_i_boxed_3576_, v_bs_3573_, v___y_3574_);
lean_dec_ref(v___y_3574_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object* v_x_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
if (lean_obj_tag(v_x_3584_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_a_3590_ = lean_ctor_get(v_x_3584_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v_x_3584_, 1);
v___x_3591_ = l_Lean_stringToMessageData(v_a_3590_);
v___x_3592_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_3591_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
return v___x_3592_;
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
v_a_3593_ = lean_ctor_get(v_x_3584_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_x_3584_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v_x_3584_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v_x_3584_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 0);
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object* v_x_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object* v_id_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; lean_object* v_env_3615_; lean_object* v_options_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3614_ = lean_st_ref_get(v___y_3612_);
v_env_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc_ref(v_env_3615_);
lean_dec(v___x_3614_);
v_options_3616_ = lean_ctor_get(v___y_3611_, 2);
v___x_3617_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3618_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3615_, v_options_3616_, v___x_3617_, v_id_3608_);
v___x_3619_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v___x_3618_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object* v_id_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object* v___x_3627_, size_t v_sz_3628_, size_t v_i_3629_, lean_object* v_bs_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
uint8_t v___x_3636_; 
v___x_3636_ = lean_usize_dec_lt(v_i_3629_, v_sz_3628_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec_ref(v___x_3627_);
v___x_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3637_, 0, v_bs_3630_);
return v___x_3637_;
}
else
{
lean_object* v_v_3638_; lean_object* v_id_3639_; lean_object* v___x_3640_; lean_object* v_bs_x27_3641_; lean_object* v_a_3643_; lean_object* v___y_3653_; uint8_t v___x_3674_; lean_object* v___x_3675_; 
v_v_3638_ = lean_array_uget(v_bs_3630_, v_i_3629_);
v_id_3639_ = lean_ctor_get(v_v_3638_, 0);
v___x_3640_ = lean_unsigned_to_nat(0u);
v_bs_x27_3641_ = lean_array_uset(v_bs_3630_, v_i_3629_, v___x_3640_);
v___x_3674_ = 0;
lean_inc(v_id_3639_);
lean_inc_ref(v___x_3627_);
v___x_3675_ = l_Lean_Environment_find_x3f(v___x_3627_, v_id_3639_, v___x_3674_);
if (lean_obj_tag(v___x_3675_) == 0)
{
v___y_3653_ = v___x_3675_;
goto v___jp_3652_;
}
else
{
lean_object* v_val_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v_val_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_val_3676_);
v___x_3677_ = l_Lean_ConstantInfo_type(v_val_3676_);
lean_dec(v_val_3676_);
v___x_3678_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3679_ = l_Lean_Expr_isConstOf(v___x_3677_, v___x_3678_);
lean_dec_ref(v___x_3677_);
if (v___x_3679_ == 0)
{
lean_dec_ref_known(v___x_3675_, 1);
goto v___jp_3650_;
}
else
{
v___y_3653_ = v___x_3675_;
goto v___jp_3652_;
}
}
v___jp_3642_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v___x_3644_ = lean_box(0);
v___x_3645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3645_, 0, v_v_3638_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
lean_ctor_set(v___x_3645_, 2, v_a_3643_);
v___x_3646_ = ((size_t)1ULL);
v___x_3647_ = lean_usize_add(v_i_3629_, v___x_3646_);
v___x_3648_ = lean_array_uset(v_bs_x27_3641_, v_i_3629_, v___x_3645_);
v_i_3629_ = v___x_3647_;
v_bs_3630_ = v___x_3648_;
goto _start;
}
v___jp_3650_:
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_box(0);
v_a_3643_ = v___x_3651_;
goto v___jp_3642_;
}
v___jp_3652_:
{
if (lean_obj_tag(v___y_3653_) == 0)
{
goto v___jp_3650_;
}
else
{
lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3672_; 
v_isSharedCheck_3672_ = !lean_is_exclusive(v___y_3653_);
if (v_isSharedCheck_3672_ == 0)
{
lean_object* v_unused_3673_; 
v_unused_3673_ = lean_ctor_get(v___y_3653_, 0);
lean_dec(v_unused_3673_);
v___x_3655_ = v___y_3653_;
v_isShared_3656_ = v_isSharedCheck_3672_;
goto v_resetjp_3654_;
}
else
{
lean_dec(v___y_3653_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3672_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v_id_3657_; lean_object* v___x_3658_; 
v_id_3657_ = lean_ctor_get(v_v_3638_, 0);
lean_inc(v_id_3657_);
v___x_3658_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3657_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v_name_3660_; lean_object* v___x_3662_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v_name_3660_ = lean_ctor_get(v_a_3659_, 0);
lean_inc_ref(v_name_3660_);
lean_dec(v_a_3659_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v_name_3660_);
v___x_3662_ = v___x_3655_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_name_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
v_a_3643_ = v___x_3662_;
goto v___jp_3642_;
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_del_object(v___x_3655_);
lean_dec_ref(v_bs_x27_3641_);
lean_dec(v_v_3638_);
lean_dec_ref(v___x_3627_);
v_a_3664_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3658_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3658_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object* v___x_3680_, lean_object* v_sz_3681_, lean_object* v_i_3682_, lean_object* v_bs_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
size_t v_sz_boxed_3689_; size_t v_i_boxed_3690_; lean_object* v_res_3691_; 
v_sz_boxed_3689_ = lean_unbox_usize(v_sz_3681_);
lean_dec(v_sz_3681_);
v_i_boxed_3690_ = lean_unbox_usize(v_i_3682_);
lean_dec(v_i_3682_);
v_res_3691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3680_, v_sz_boxed_3689_, v_i_boxed_3690_, v_bs_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object* v___x_3692_, lean_object* v___x_3693_, size_t v_sz_3694_, size_t v_i_3695_, lean_object* v_bs_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
uint8_t v___x_3702_; 
v___x_3702_ = lean_usize_dec_lt(v_i_3695_, v_sz_3694_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; 
lean_dec_ref(v___x_3693_);
lean_dec_ref(v___x_3692_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_bs_3696_);
return v___x_3703_;
}
else
{
lean_object* v_v_3704_; lean_object* v_toWidgetInstance_3705_; lean_object* v_stx_3706_; lean_object* v_id_3707_; lean_object* v___x_3708_; lean_object* v_bs_x27_3709_; lean_object* v___y_3711_; lean_object* v___y_3712_; uint8_t v___x_3718_; lean_object* v_a_3720_; lean_object* v___y_3735_; lean_object* v___x_3755_; 
v_v_3704_ = lean_array_uget_borrowed(v_bs_3696_, v_i_3695_);
v_toWidgetInstance_3705_ = lean_ctor_get(v_v_3704_, 0);
lean_inc_ref(v_toWidgetInstance_3705_);
v_stx_3706_ = lean_ctor_get(v_v_3704_, 1);
lean_inc(v_stx_3706_);
v_id_3707_ = lean_ctor_get(v_toWidgetInstance_3705_, 0);
v___x_3708_ = lean_unsigned_to_nat(0u);
v_bs_x27_3709_ = lean_array_uset(v_bs_3696_, v_i_3695_, v___x_3708_);
v___x_3718_ = 0;
lean_inc(v_id_3707_);
lean_inc_ref(v___x_3693_);
v___x_3755_ = l_Lean_Environment_find_x3f(v___x_3693_, v_id_3707_, v___x_3718_);
if (lean_obj_tag(v___x_3755_) == 0)
{
v___y_3735_ = v___x_3755_;
goto v___jp_3734_;
}
else
{
lean_object* v_val_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_val_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_val_3756_);
v___x_3757_ = l_Lean_ConstantInfo_type(v_val_3756_);
lean_dec(v_val_3756_);
v___x_3758_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3759_ = l_Lean_Expr_isConstOf(v___x_3757_, v___x_3758_);
lean_dec_ref(v___x_3757_);
if (v___x_3759_ == 0)
{
lean_dec_ref_known(v___x_3755_, 1);
goto v___jp_3732_;
}
else
{
v___y_3735_ = v___x_3755_;
goto v___jp_3734_;
}
}
v___jp_3710_:
{
lean_object* v___x_3713_; size_t v___x_3714_; size_t v___x_3715_; lean_object* v___x_3716_; 
v___x_3713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3713_, 0, v_toWidgetInstance_3705_);
lean_ctor_set(v___x_3713_, 1, v___y_3712_);
lean_ctor_set(v___x_3713_, 2, v___y_3711_);
v___x_3714_ = ((size_t)1ULL);
v___x_3715_ = lean_usize_add(v_i_3695_, v___x_3714_);
v___x_3716_ = lean_array_uset(v_bs_x27_3709_, v_i_3695_, v___x_3713_);
v_i_3695_ = v___x_3715_;
v_bs_3696_ = v___x_3716_;
goto _start;
}
v___jp_3719_:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_Syntax_getRange_x3f(v_stx_3706_, v___x_3718_);
lean_dec(v_stx_3706_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_box(0);
v___y_3711_ = v_a_3720_;
v___y_3712_ = v___x_3722_;
goto v___jp_3710_;
}
else
{
lean_object* v_val_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3731_; 
v_val_3723_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3725_ = v___x_3721_;
v_isShared_3726_ = v_isSharedCheck_3731_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_val_3723_);
lean_dec(v___x_3721_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3731_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_inc_ref(v___x_3692_);
v___x_3727_ = l_Lean_Syntax_Range_toLspRange(v___x_3692_, v_val_3723_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3727_);
v___x_3729_ = v___x_3725_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
v___y_3711_ = v_a_3720_;
v___y_3712_ = v___x_3729_;
goto v___jp_3710_;
}
}
}
}
v___jp_3732_:
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_box(0);
v_a_3720_ = v___x_3733_;
goto v___jp_3719_;
}
v___jp_3734_:
{
if (lean_obj_tag(v___y_3735_) == 0)
{
goto v___jp_3732_;
}
else
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3753_; 
v_isSharedCheck_3753_ = !lean_is_exclusive(v___y_3735_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; 
v_unused_3754_ = lean_ctor_get(v___y_3735_, 0);
lean_dec(v_unused_3754_);
v___x_3737_ = v___y_3735_;
v_isShared_3738_ = v_isSharedCheck_3753_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v___y_3735_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3753_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; 
lean_inc(v_id_3707_);
v___x_3739_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3707_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v_name_3741_; lean_object* v___x_3743_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v_name_3741_ = lean_ctor_get(v_a_3740_, 0);
lean_inc_ref(v_name_3741_);
lean_dec(v_a_3740_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_name_3741_);
v___x_3743_ = v___x_3737_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_name_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
v_a_3720_ = v___x_3743_;
goto v___jp_3719_;
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_del_object(v___x_3737_);
lean_dec_ref(v_bs_x27_3709_);
lean_dec(v_stx_3706_);
lean_dec_ref(v_toWidgetInstance_3705_);
lean_dec_ref(v___x_3693_);
lean_dec_ref(v___x_3692_);
v_a_3745_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3739_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3739_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object* v___x_3760_, lean_object* v___x_3761_, lean_object* v_sz_3762_, lean_object* v_i_3763_, lean_object* v_bs_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
size_t v_sz_boxed_3770_; size_t v_i_boxed_3771_; lean_object* v_res_3772_; 
v_sz_boxed_3770_ = lean_unbox_usize(v_sz_3762_);
lean_dec(v_sz_3762_);
v_i_boxed_3771_ = lean_unbox_usize(v_i_3763_);
lean_dec(v_i_3763_);
v_res_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3760_, v___x_3761_, v_sz_boxed_3770_, v_i_boxed_3771_, v_bs_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object* v_pos_3773_, lean_object* v_text_3774_, lean_object* v_val_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = lean_st_ref_get(v___y_3779_);
v___x_3782_ = l_Lean_Widget_evalPanelWidgets(v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v_env_3784_; size_t v_sz_3785_; size_t v___x_3786_; lean_object* v___x_3787_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v_env_3784_ = lean_ctor_get(v___x_3781_, 0);
lean_inc_ref_n(v_env_3784_, 2);
lean_dec(v___x_3781_);
v_sz_3785_ = lean_array_size(v_a_3783_);
v___x_3786_ = ((size_t)0ULL);
v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v_env_3784_, v_sz_3785_, v___x_3786_, v_a_3783_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v_line_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; size_t v_sz_3792_; lean_object* v___x_3793_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3787_, 1);
v_line_3789_ = lean_ctor_get(v_pos_3773_, 0);
lean_inc(v_line_3789_);
lean_dec_ref(v_pos_3773_);
lean_inc_ref(v_text_3774_);
v___x_3790_ = l_Lean_Widget_widgetInfosAt_x3f(v_text_3774_, v_val_3775_, v_line_3789_);
v___x_3791_ = lean_array_mk(v___x_3790_);
v_sz_3792_ = lean_array_size(v___x_3791_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v_text_3774_, v_env_3784_, v_sz_3792_, v___x_3786_, v___x_3791_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3802_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = l_Array_append___redArg(v_a_3788_, v_a_3794_);
lean_dec(v_a_3794_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3800_ = v___x_3796_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v_a_3788_);
v_a_3803_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3793_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3793_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_env_3784_);
lean_dec_ref(v_val_3775_);
lean_dec_ref(v_text_3774_);
lean_dec_ref(v_pos_3773_);
v_a_3811_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3787_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3787_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v___x_3781_);
lean_dec_ref(v_val_3775_);
lean_dec_ref(v_text_3774_);
lean_dec_ref(v_pos_3773_);
v_a_3819_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3782_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3782_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object* v_pos_3827_, lean_object* v_text_3828_, lean_object* v_val_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3827_, v_text_3828_, v_val_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object* v_pos_3840_, lean_object* v_text_3841_, lean_object* v_x_3842_, lean_object* v___y_3843_){
_start:
{
if (lean_obj_tag(v_x_3842_) == 1)
{
lean_object* v_val_3848_; 
v_val_3848_ = lean_ctor_get(v_x_3842_, 0);
lean_inc(v_val_3848_);
lean_dec_ref_known(v_x_3842_, 1);
if (lean_obj_tag(v_val_3848_) == 0)
{
lean_object* v_i_3849_; 
v_i_3849_ = lean_ctor_get(v_val_3848_, 0);
if (lean_obj_tag(v_i_3849_) == 0)
{
lean_object* v_info_3850_; lean_object* v___f_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_info_3850_ = lean_ctor_get(v_i_3849_, 0);
lean_inc_ref(v_info_3850_);
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3851_, 0, v_pos_3840_);
lean_closure_set(v___f_3851_, 1, v_text_3841_);
lean_closure_set(v___f_3851_, 2, v_val_3848_);
v___x_3852_ = lean_box(0);
v___x_3853_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__1));
v___x_3854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3854_, 0, v_info_3850_);
lean_ctor_set(v___x_3854_, 1, v___x_3852_);
lean_ctor_set(v___x_3854_, 2, v___x_3853_);
v___x_3855_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2_);
v___x_3856_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_3854_, v___x_3855_, v___f_3851_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3873_; 
v_a_3865_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3867_ = v___x_3856_;
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3856_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3869_ = l_Lean_Server_RequestError_ofIoError(v_a_3865_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3869_);
v___x_3871_ = v___x_3867_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_dec_ref_known(v_val_3848_, 2);
lean_dec_ref(v_text_3841_);
lean_dec_ref(v_pos_3840_);
goto v___jp_3845_;
}
}
else
{
lean_dec(v_val_3848_);
lean_dec_ref(v_text_3841_);
lean_dec_ref(v_pos_3840_);
goto v___jp_3845_;
}
}
else
{
lean_dec(v_x_3842_);
lean_dec_ref(v_text_3841_);
lean_dec_ref(v_pos_3840_);
goto v___jp_3845_;
}
v___jp_3845_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__0));
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object* v_pos_3874_, lean_object* v_text_3875_, lean_object* v_x_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3874_, v_text_3875_, v_x_3876_, v___y_3877_);
lean_dec_ref(v___y_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets(lean_object* v_pos_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3883_; lean_object* v_a_3884_; lean_object* v_toEditableDocumentCore_3885_; lean_object* v_meta_3886_; lean_object* v_text_3887_; lean_object* v___f_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3883_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_3881_);
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref(v___x_3883_);
v_toEditableDocumentCore_3885_ = lean_ctor_get(v_a_3884_, 0);
v_meta_3886_ = lean_ctor_get(v_toEditableDocumentCore_3885_, 0);
v_text_3887_ = lean_ctor_get(v_meta_3886_, 3);
lean_inc_ref(v_text_3887_);
lean_inc_ref(v_pos_3880_);
v___f_3888_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3888_, 0, v_pos_3880_);
lean_closure_set(v___f_3888_, 1, v_text_3887_);
v___x_3889_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3887_, v_pos_3880_);
v___x_3890_ = 1;
v___x_3891_ = l_Lean_Server_RequestM_findInfoTreeAtPos(v_a_3884_, v___x_3889_, v___x_3890_);
v___x_3892_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3891_, v___f_3888_, v_a_3881_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object* v_pos_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Widget_getWidgets(v_pos_3893_, v_a_3894_);
lean_dec_ref(v_a_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object* v_00_u03b1_3897_, lean_object* v_x_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3905_, lean_object* v_x_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(v_00_u03b1_3905_, v_x_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object* v_val_3913_, lean_object* v___f_3914_, lean_object* v_x_3915_, lean_object* v___y_3916_){
_start:
{
if (lean_obj_tag(v_x_3915_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v___f_3914_);
v_a_3918_ = lean_ctor_get(v_x_3915_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_x_3915_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v_x_3915_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v_x_3915_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 1);
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3942_; 
v_a_3926_ = lean_ctor_get(v_x_3915_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_x_3915_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3928_ = v_x_3915_;
v_isShared_3929_ = v_isSharedCheck_3942_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v_x_3915_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3942_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3930_; lean_object* v_objects_3931_; lean_object* v_expireTime_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v_fst_3936_; lean_object* v_snd_3937_; lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3930_ = lean_st_ref_take(v_val_3913_);
v_objects_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc_ref(v_objects_3931_);
v_expireTime_3932_ = lean_ctor_get(v___x_3930_, 1);
lean_inc(v_expireTime_3932_);
lean_dec(v___x_3930_);
v___f_3933_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_3933_, 0, v_expireTime_3932_);
v___x_3934_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_a_3926_, v_objects_3931_);
v___x_3935_ = l_Prod_map___redArg(v___f_3914_, v___f_3933_, v___x_3934_);
v_fst_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_fst_3936_);
v_snd_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_snd_3937_);
lean_dec_ref(v___x_3935_);
v___x_3938_ = lean_st_ref_set(v_val_3913_, v_snd_3937_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set_tag(v___x_3928_, 0);
lean_ctor_set(v___x_3928_, 0, v_fst_3936_);
v___x_3940_ = v___x_3928_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_fst_3936_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object* v_val_3943_, lean_object* v___f_3944_, lean_object* v_x_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_3943_, v___f_3944_, v_x_3945_, v___y_3946_);
lean_dec_ref(v___y_3946_);
lean_dec(v_val_3943_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object* v_method_3949_, lean_object* v_handler_3950_, lean_object* v___f_3951_, uint64_t v_seshId_3952_, lean_object* v_j_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_rpcSessions_3956_; lean_object* v___x_3957_; 
v_rpcSessions_3956_ = lean_ctor_get(v___y_3954_, 0);
v___x_3957_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_3570059497____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_3956_, v_seshId_3952_);
if (lean_obj_tag(v___x_3957_) == 1)
{
lean_object* v_val_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_val_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_val_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_st_ref_get(v_val_3958_);
lean_dec(v___x_3959_);
lean_inc(v_j_3953_);
v___x_3960_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v_j_3953_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v_val_3958_);
lean_dec_ref(v___f_3951_);
lean_dec_ref(v_handler_3950_);
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3981_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3981_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
uint8_t v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3965_ = 3;
v___x_3966_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_3967_ = 1;
v___x_3968_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_3949_, v___x_3967_);
v___x_3969_ = lean_string_append(v___x_3966_, v___x_3968_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_3971_ = lean_string_append(v___x_3969_, v___x_3970_);
v___x_3972_ = l_Lean_Json_compress(v_j_3953_);
v___x_3973_ = lean_string_append(v___x_3971_, v___x_3972_);
lean_dec_ref(v___x_3972_);
v___x_3974_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_3975_ = lean_string_append(v___x_3973_, v___x_3974_);
v___x_3976_ = lean_string_append(v___x_3975_, v_a_3961_);
lean_dec(v_a_3961_);
v___x_3977_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*1, v___x_3965_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set_tag(v___x_3963_, 1);
lean_ctor_set(v___x_3963_, 0, v___x_3977_);
v___x_3979_ = v___x_3963_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3983_; 
lean_dec(v_j_3953_);
lean_dec(v_method_3949_);
v_a_3982_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3960_, 1);
lean_inc_ref(v___y_3954_);
v___x_3983_ = lean_apply_3(v_handler_3950_, v_a_3982_, v___y_3954_, lean_box(0));
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___f_3985_; lean_object* v___x_3986_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v___f_3985_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3985_, 0, v_val_3958_);
lean_closure_set(v___f_3985_, 1, v___f_3951_);
v___x_3986_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_3984_, v___f_3985_, v___y_3954_);
return v___x_3986_;
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v_val_3958_);
lean_dec_ref(v___f_3951_);
v_a_3987_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3983_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3983_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec(v___x_3957_);
lean_dec(v_j_3953_);
lean_dec_ref(v___f_3951_);
lean_dec_ref(v_handler_3950_);
lean_dec(v_method_3949_);
v___x_3995_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
return v___x_3996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_method_3997_, lean_object* v_handler_3998_, lean_object* v___f_3999_, lean_object* v_seshId_4000_, lean_object* v_j_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
uint64_t v_seshId_boxed_4004_; lean_object* v_res_4005_; 
v_seshId_boxed_4004_ = lean_unbox_uint64(v_seshId_4000_);
lean_dec_ref(v_seshId_4000_);
v_res_4005_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_method_3997_, v_handler_3998_, v___f_3999_, v_seshId_boxed_4004_, v_j_4001_, v___y_4002_);
lean_dec_ref(v___y_4002_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_4006_, lean_object* v_handler_4007_){
_start:
{
lean_object* v___f_4008_; lean_object* v___f_4009_; 
v___f_4008_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_4009_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4009_, 0, v_method_4006_);
lean_closure_set(v___f_4009_, 1, v_handler_4007_);
lean_closure_set(v___f_4009_, 2, v___f_4008_);
return v___f_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object* v_method_4010_, lean_object* v_handler_4011_){
_start:
{
uint8_t v___x_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v_errMsg_4019_; 
v___x_4013_ = l_Lean_initializing();
v___x_4014_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_4015_ = 1;
lean_inc(v_method_4010_);
v___x_4016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_4010_, v___x_4015_);
v___x_4017_ = lean_string_append(v___x_4014_, v___x_4016_);
lean_dec_ref(v___x_4016_);
v___x_4018_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_4019_ = lean_string_append(v___x_4017_, v___x_4018_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec_ref(v_handler_4011_);
lean_dec(v_method_4010_);
v___x_4020_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_4021_ = lean_string_append(v_errMsg_4019_, v___x_4020_);
v___x_4022_ = lean_mk_io_user_error(v___x_4021_);
v___x_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
return v___x_4023_;
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; uint8_t v___x_4026_; 
v___x_4024_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_4025_ = lean_st_ref_get(v___x_4024_);
v___x_4026_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4025_, v_method_4010_);
lean_dec(v___x_4025_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_dec_ref(v_errMsg_4019_);
v___x_4027_ = lean_st_ref_take(v___x_4024_);
lean_inc(v_method_4010_);
v___x_4028_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(v_method_4010_, v_handler_4011_);
v___x_4029_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4027_, v_method_4010_, v___x_4028_);
v___x_4030_ = lean_st_ref_set(v___x_4024_, v___x_4029_);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
else
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_dec_ref(v_handler_4011_);
lean_dec(v_method_4010_);
v___x_4032_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_4033_ = lean_string_append(v_errMsg_4019_, v___x_4032_);
v___x_4034_ = lean_mk_io_user_error(v___x_4033_);
v___x_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4036_, lean_object* v_handler_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_4036_, v_handler_4037_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4048_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4049_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v___x_4047_, v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
return v_res_4051_;
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
