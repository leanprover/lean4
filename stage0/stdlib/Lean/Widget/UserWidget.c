// Lean compiler output
// Module: Lean.Widget.UserWidget
// Imports: public import Lean.Elab.Eval public import Lean.Server.Rpc.RequestHandling import Lean.Language.Lean.Util
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "addBuiltinModule"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "A widget module with the same hash (JS source code) was already registered at "};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToModule"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toModule"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__7_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "A builtin widget module with the same hash (JS source code) was already registered."};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__7_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__7_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "widgetModuleAttrImpl"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 203, 59, 214, 15, 221, 203, 217)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "Registers a widget module. Its type must implement Lean.Widget.ToModule."};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_widget_module"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 42, 123, 194, 197, 140, 191, 110)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "widget_module"};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 72, 138, 198, 227, 75, 129, 42)}};
static const lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedWidgetSource_default = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instInhabitedWidgetSource = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Lean_Widget_instInhabitedUserWidgetDefinition_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__value;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29__value;
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
v_k_74_ = lean_ctor_get(v_impl_70_, 1);
v_v_75_ = lean_ctor_get(v_impl_70_, 2);
v_l_76_ = lean_ctor_get(v_impl_70_, 3);
lean_inc(v_l_76_);
v_r_77_ = lean_ctor_get(v_impl_70_, 4);
v___x_78_ = lean_unsigned_to_nat(3u);
v___x_79_ = lean_nat_mul(v___x_78_, v_size_72_);
v___x_80_ = lean_nat_dec_lt(v___x_79_, v_size_73_);
lean_dec(v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_l_76_);
v___x_81_ = lean_nat_add(v___x_71_, v_size_72_);
v___x_82_ = lean_nat_add(v___x_81_, v_size_73_);
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
lean_inc(v_r_77_);
lean_inc(v_v_75_);
lean_inc(v_k_74_);
lean_inc(v_size_73_);
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
v_k_213_ = lean_ctor_get(v_impl_209_, 1);
v_v_214_ = lean_ctor_get(v_impl_209_, 2);
v_l_215_ = lean_ctor_get(v_impl_209_, 3);
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
v___x_220_ = lean_nat_add(v___x_210_, v_size_212_);
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
lean_inc(v_l_215_);
lean_inc(v_v_214_);
lean_inc(v_k_213_);
lean_inc(v_size_212_);
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
if (lean_obj_tag(v_l_296_) == 0)
{
lean_object* v_r_297_; lean_object* v_k_298_; lean_object* v_v_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
lean_inc_ref(v_l_296_);
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
lean_inc(v_l_296_);
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
v___x_363_ = lean_st_ref_put(v___x_358_, v___x_362_);
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
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_));
v___x_514_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
return v_res_516_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_517_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_523_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
lean_ctor_set(v___x_523_, 3, v___x_522_);
lean_ctor_set(v___x_523_, 4, v___x_522_);
lean_ctor_set(v___x_523_, 5, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; lean_object* v_nextMacroScope_529_; lean_object* v_ngen_530_; lean_object* v_auxDeclNGen_531_; lean_object* v_traceState_532_; lean_object* v_recordedDeps_533_; lean_object* v_messages_534_; lean_object* v_infoState_535_; lean_object* v_snapshotTasks_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_562_; 
v___x_528_ = lean_st_ref_take(v___y_526_);
v_nextMacroScope_529_ = lean_ctor_get(v___x_528_, 1);
v_ngen_530_ = lean_ctor_get(v___x_528_, 2);
v_auxDeclNGen_531_ = lean_ctor_get(v___x_528_, 3);
v_traceState_532_ = lean_ctor_get(v___x_528_, 4);
v_recordedDeps_533_ = lean_ctor_get(v___x_528_, 6);
v_messages_534_ = lean_ctor_get(v___x_528_, 7);
v_infoState_535_ = lean_ctor_get(v___x_528_, 8);
v_snapshotTasks_536_ = lean_ctor_get(v___x_528_, 9);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; lean_object* v_unused_564_; 
v_unused_563_ = lean_ctor_get(v___x_528_, 5);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v___x_528_, 0);
lean_dec(v_unused_564_);
v___x_538_ = v___x_528_;
v_isShared_539_ = v_isSharedCheck_562_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snapshotTasks_536_);
lean_inc(v_infoState_535_);
lean_inc(v_messages_534_);
lean_inc(v_recordedDeps_533_);
lean_inc(v_traceState_532_);
lean_inc(v_auxDeclNGen_531_);
lean_inc(v_ngen_530_);
lean_inc(v_nextMacroScope_529_);
lean_dec(v___x_528_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_562_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 5, v___x_540_);
lean_ctor_set(v___x_538_, 0, v_env_524_);
v___x_542_ = v___x_538_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_env_524_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_529_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_530_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_531_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_traceState_532_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_recordedDeps_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_messages_534_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_infoState_535_);
lean_ctor_set(v_reuseFailAlloc_561_, 9, v_snapshotTasks_536_);
v___x_542_ = v_reuseFailAlloc_561_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_mctx_545_; lean_object* v_zetaDeltaFVarIds_546_; lean_object* v_postponed_547_; lean_object* v_diag_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v___x_543_ = lean_st_ref_put(v___y_526_, v___x_542_);
v___x_544_ = lean_st_ref_take(v___y_525_);
v_mctx_545_ = lean_ctor_get(v___x_544_, 0);
v_zetaDeltaFVarIds_546_ = lean_ctor_get(v___x_544_, 2);
v_postponed_547_ = lean_ctor_get(v___x_544_, 3);
v_diag_548_ = lean_ctor_get(v___x_544_, 4);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_544_, 1);
lean_dec(v_unused_560_);
v___x_550_ = v___x_544_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_diag_548_);
lean_inc(v_postponed_547_);
lean_inc(v_zetaDeltaFVarIds_546_);
lean_inc(v_mctx_545_);
lean_dec(v___x_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_553_);
v___x_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_mctx_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_zetaDeltaFVarIds_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_postponed_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_diag_548_);
v___x_555_ = v_reuseFailAlloc_558_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_st_ref_put(v___y_525_, v___x_555_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_552_);
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec(v___y_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(lean_object* v_env_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_570_, v___y_572_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(v_env_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_586_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_587_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
lean_ctor_set(v___x_589_, 2, v___x_588_);
lean_ctor_set(v___x_589_, 3, v___x_588_);
lean_ctor_set(v___x_589_, 4, v___x_587_);
lean_ctor_set(v___x_589_, 5, v___x_587_);
lean_ctor_set(v___x_589_, 6, v___x_587_);
lean_ctor_set(v___x_589_, 7, v___x_587_);
lean_ctor_set(v___x_589_, 8, v___x_587_);
lean_ctor_set(v___x_589_, 9, v___x_587_);
lean_ctor_set(v___x_589_, 10, v___x_587_);
lean_ctor_set(v___x_589_, 11, v___x_586_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(32u);
v___x_591_ = lean_mk_empty_array_with_capacity(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_593_ = ((size_t)5ULL);
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_unsigned_to_nat(32u);
v___x_596_ = lean_mk_empty_array_with_capacity(v___x_595_);
v___x_597_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_598_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___x_594_);
lean_ctor_set(v___x_598_, 3, v___x_594_);
lean_ctor_set_usize(v___x_598_, 4, v___x_593_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_box(1);
v___x_600_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v_toCold_608_; lean_object* v_env_609_; lean_object* v_options_610_; uint8_t v___x_611_; lean_object* v_env_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_607_ = lean_st_ref_get(v___y_605_);
v_toCold_608_ = lean_ctor_get(v___y_604_, 0);
v_env_609_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_env_609_);
lean_dec(v___x_607_);
v_options_610_ = lean_ctor_get(v_toCold_608_, 2);
v___x_611_ = 0;
v_env_612_ = l_Lean_Environment_setRecordingDeps(v_env_609_, v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_614_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_610_);
v___x_615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_615_, 0, v_env_612_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
lean_ctor_set(v___x_615_, 3, v_options_610_);
v___x_616_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_msgData_603_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msgData_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_ref_627_; lean_object* v___x_628_; lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_ref_627_ = lean_ctor_get(v___y_624_, 2);
v___x_628_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msg_623_, v___y_624_, v___y_625_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_inc(v_ref_627_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_ref_627_);
lean_ctor_set(v___x_633_, 1, v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 1);
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v_name_649_, lean_object* v_decl_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_654_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_655_ = l_Lean_MessageData_ofName(v_name_649_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v___x_658_, v___y_651_, v___y_652_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_name_660_, lean_object* v_decl_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_name_660_, v_decl_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v_decl_661_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_s_668_){
_start:
{
lean_object* v_addEntryFn_669_; lean_object* v_importedEntries_670_; lean_object* v_state_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_addEntryFn_669_ = lean_ctor_get(v___x_666_, 3);
lean_inc(v_addEntryFn_669_);
lean_dec_ref(v___x_666_);
v_importedEntries_670_ = lean_ctor_get(v_s_668_, 0);
v_state_671_ = lean_ctor_get(v_s_668_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_s_668_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v_s_668_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_state_671_);
lean_inc(v_importedEntries_670_);
lean_dec(v_s_668_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_state_675_; lean_object* v___x_677_; 
v_state_675_ = lean_apply_2(v_addEntryFn_669_, v_state_671_, v___x_667_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_state_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_importedEntries_670_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_state_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_680_, uint64_t v_k_681_){
_start:
{
if (lean_obj_tag(v_t_680_) == 0)
{
lean_object* v_k_682_; lean_object* v_v_683_; lean_object* v_l_684_; lean_object* v_r_685_; uint64_t v___x_686_; uint8_t v___x_687_; 
v_k_682_ = lean_ctor_get(v_t_680_, 1);
v_v_683_ = lean_ctor_get(v_t_680_, 2);
v_l_684_ = lean_ctor_get(v_t_680_, 3);
v_r_685_ = lean_ctor_get(v_t_680_, 4);
v___x_686_ = lean_unbox_uint64(v_k_682_);
v___x_687_ = lean_uint64_dec_lt(v_k_681_, v___x_686_);
if (v___x_687_ == 0)
{
uint64_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unbox_uint64(v_k_682_);
v___x_689_ = lean_uint64_dec_eq(v_k_681_, v___x_688_);
if (v___x_689_ == 0)
{
v_t_680_ = v_r_685_;
goto _start;
}
else
{
lean_object* v___x_691_; 
lean_inc(v_v_683_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_v_683_);
return v___x_691_;
}
}
else
{
v_t_680_ = v_l_684_;
goto _start;
}
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(0);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_694_, lean_object* v_k_695_){
_start:
{
uint64_t v_k_boxed_696_; lean_object* v_res_697_; 
v_k_boxed_696_ = lean_unbox_uint64(v_k_695_);
lean_dec_ref(v_k_695_);
v_res_697_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_694_, v_k_boxed_696_);
lean_dec(v_t_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_msgData_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; lean_object* v_env_705_; uint8_t v___x_706_; lean_object* v_env_707_; lean_object* v___x_708_; lean_object* v_toCold_709_; lean_object* v_mctx_710_; lean_object* v_lctx_711_; lean_object* v_options_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_704_ = lean_st_ref_get(v___y_702_);
v_env_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_env_705_);
lean_dec(v___x_704_);
v___x_706_ = 0;
v_env_707_ = l_Lean_Environment_setRecordingDeps(v_env_705_, v___x_706_);
v___x_708_ = lean_st_ref_get(v___y_700_);
v_toCold_709_ = lean_ctor_get(v___y_701_, 0);
v_mctx_710_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_mctx_710_);
lean_dec(v___x_708_);
v_lctx_711_ = lean_ctor_get(v___y_699_, 2);
v_options_712_ = lean_ctor_get(v_toCold_709_, 2);
lean_inc_ref(v_options_712_);
lean_inc_ref(v_lctx_711_);
v___x_713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_713_, 0, v_env_707_);
lean_ctor_set(v___x_713_, 1, v_mctx_710_);
lean_ctor_set(v___x_713_, 2, v_lctx_711_);
lean_ctor_set(v___x_713_, 3, v_options_712_);
v___x_714_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_msgData_698_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msgData_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_ref_729_; lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_ref_729_ = lean_ctor_get(v___y_726_, 2);
v___x_730_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_ref_729_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_ref_729_);
lean_ctor_set(v___x_735_, 1, v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 1);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_759_, uint8_t v_kind_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___y_772_; 
v___x_766_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_767_ = l_Lean_MessageData_ofName(v_name_759_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
switch(v_kind_760_)
{
case 0:
{
lean_object* v___x_779_; 
v___x_779_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_772_ = v___x_779_;
goto v___jp_771_;
}
case 1:
{
lean_object* v___x_780_; 
v___x_780_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_772_ = v___x_780_;
goto v___jp_771_;
}
default: 
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_772_ = v___x_781_;
goto v___jp_771_;
}
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_ref(v___y_772_);
v___x_773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_773_, 0, v___y_772_);
v___x_774_ = l_Lean_MessageData_ofFormat(v___x_773_);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_770_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_777_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_782_, lean_object* v_kind_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v_kind_boxed_789_; lean_object* v_res_790_; 
v_kind_boxed_789_ = lean_unbox(v_kind_783_);
v_res_790_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_782_, v_kind_boxed_789_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t v_suppressElabErrors_799_, uint8_t v___y_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_801_) == 1)
{
lean_object* v_pre_802_; 
v_pre_802_ = lean_ctor_get(v_x_801_, 0);
switch(lean_obj_tag(v_pre_802_))
{
case 1:
{
lean_object* v_pre_803_; 
v_pre_803_ = lean_ctor_get(v_pre_802_, 0);
switch(lean_obj_tag(v_pre_803_))
{
case 0:
{
lean_object* v_str_804_; lean_object* v_str_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_str_804_ = lean_ctor_get(v_x_801_, 1);
v_str_805_ = lean_ctor_get(v_pre_802_, 1);
v___x_806_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_807_ = lean_string_dec_eq(v_str_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_809_ = lean_string_dec_eq(v_str_805_, v___x_808_);
if (v___x_809_ == 0)
{
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_811_ = lean_string_dec_eq(v_str_804_, v___x_810_);
if (v___x_811_ == 0)
{
return v___x_811_;
}
else
{
return v_suppressElabErrors_799_;
}
}
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_813_ = lean_string_dec_eq(v_str_804_, v___x_812_);
if (v___x_813_ == 0)
{
return v___x_813_;
}
else
{
return v_suppressElabErrors_799_;
}
}
}
case 1:
{
lean_object* v_pre_814_; 
v_pre_814_ = lean_ctor_get(v_pre_803_, 0);
if (lean_obj_tag(v_pre_814_) == 0)
{
lean_object* v_str_815_; lean_object* v_str_816_; lean_object* v_str_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_str_815_ = lean_ctor_get(v_x_801_, 1);
v_str_816_ = lean_ctor_get(v_pre_802_, 1);
v_str_817_ = lean_ctor_get(v_pre_803_, 1);
v___x_818_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_819_ = lean_string_dec_eq(v_str_817_, v___x_818_);
if (v___x_819_ == 0)
{
return v___x_819_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_821_ = lean_string_dec_eq(v_str_816_, v___x_820_);
if (v___x_821_ == 0)
{
return v___x_821_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6));
v___x_823_ = lean_string_dec_eq(v_str_815_, v___x_822_);
if (v___x_823_ == 0)
{
return v___x_823_;
}
else
{
return v_suppressElabErrors_799_;
}
}
}
}
else
{
return v___y_800_;
}
}
default: 
{
return v___y_800_;
}
}
}
case 0:
{
lean_object* v_str_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_str_824_ = lean_ctor_get(v_x_801_, 1);
v___x_825_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7));
v___x_826_ = lean_string_dec_eq(v_str_824_, v___x_825_);
if (v___x_826_ == 0)
{
return v___x_826_;
}
else
{
return v_suppressElabErrors_799_;
}
}
default: 
{
return v___y_800_;
}
}
}
else
{
return v___y_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_827_, lean_object* v___y_828_, lean_object* v_x_829_){
_start:
{
uint8_t v_suppressElabErrors_boxed_830_; uint8_t v___y_11199__boxed_831_; uint8_t v_res_832_; lean_object* v_r_833_; 
v_suppressElabErrors_boxed_830_ = lean_unbox(v_suppressElabErrors_827_);
v___y_11199__boxed_831_ = lean_unbox(v___y_828_);
v_res_832_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_boxed_830_, v___y_11199__boxed_831_, v_x_829_);
lean_dec(v_x_829_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_opts_834_, lean_object* v_opt_835_){
_start:
{
lean_object* v_name_836_; lean_object* v_defValue_837_; lean_object* v_map_838_; lean_object* v___x_839_; 
v_name_836_ = lean_ctor_get(v_opt_835_, 0);
v_defValue_837_ = lean_ctor_get(v_opt_835_, 1);
v_map_838_ = lean_ctor_get(v_opts_834_, 0);
v___x_839_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_838_, v_name_836_);
if (lean_obj_tag(v___x_839_) == 0)
{
uint8_t v___x_840_; 
v___x_840_ = lean_unbox(v_defValue_837_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; 
v_val_841_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_839_, 1);
if (lean_obj_tag(v_val_841_) == 1)
{
uint8_t v_v_842_; 
v_v_842_ = lean_ctor_get_uint8(v_val_841_, 0);
lean_dec_ref_known(v_val_841_, 0);
return v_v_842_;
}
else
{
uint8_t v___x_843_; 
lean_dec(v_val_841_);
v___x_843_ = lean_unbox(v_defValue_837_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_opts_844_, lean_object* v_opt_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_opts_844_, v_opt_845_);
lean_dec_ref(v_opt_845_);
lean_dec_ref(v_opts_844_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_ref_849_, lean_object* v_msgData_850_, uint8_t v_severity_851_, uint8_t v_isSilent_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; uint8_t v___y_862_; uint8_t v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v_toCold_866_; lean_object* v___y_867_; lean_object* v___y_896_; lean_object* v___y_897_; uint8_t v___y_898_; lean_object* v___y_899_; uint8_t v___y_900_; uint8_t v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; uint8_t v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; uint8_t v___y_926_; lean_object* v___y_927_; uint8_t v___y_928_; lean_object* v___y_929_; uint8_t v___y_933_; uint8_t v___y_934_; uint8_t v___y_935_; uint8_t v___x_946_; uint8_t v___y_948_; uint8_t v___y_949_; uint8_t v___y_950_; uint8_t v___y_952_; uint8_t v___x_960_; 
v___x_946_ = 2;
v___x_960_ = l_Lean_instBEqMessageSeverity_beq(v_severity_851_, v___x_946_);
if (v___x_960_ == 0)
{
v___y_952_ = v___x_960_;
goto v___jp_951_;
}
else
{
uint8_t v___x_961_; 
lean_inc_ref(v_msgData_850_);
v___x_961_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_850_);
v___y_952_ = v___x_961_;
goto v___jp_951_;
}
v___jp_858_:
{
lean_object* v_currNamespace_868_; lean_object* v_openDecls_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_env_874_; lean_object* v_nextMacroScope_875_; lean_object* v_ngen_876_; lean_object* v_auxDeclNGen_877_; lean_object* v_traceState_878_; lean_object* v_cache_879_; lean_object* v_recordedDeps_880_; lean_object* v_messages_881_; lean_object* v_infoState_882_; lean_object* v_snapshotTasks_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_894_; 
v_currNamespace_868_ = lean_ctor_get(v_toCold_866_, 4);
v_openDecls_869_ = lean_ctor_get(v_toCold_866_, 5);
lean_inc(v_openDecls_869_);
lean_inc(v_currNamespace_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_currNamespace_868_);
lean_ctor_set(v___x_870_, 1, v_openDecls_869_);
v___x_871_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc_ref(v___y_865_);
v___x_872_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_872_, 0, v___y_865_);
lean_ctor_set(v___x_872_, 1, v___y_864_);
lean_ctor_set(v___x_872_, 2, v___y_861_);
lean_ctor_set(v___x_872_, 3, v___y_859_);
lean_ctor_set(v___x_872_, 4, v___x_871_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*5, v___y_862_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*5 + 1, v___y_863_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*5 + 2, v_isSilent_852_);
v___x_873_ = lean_st_ref_take(v___y_867_);
v_env_874_ = lean_ctor_get(v___x_873_, 0);
v_nextMacroScope_875_ = lean_ctor_get(v___x_873_, 1);
v_ngen_876_ = lean_ctor_get(v___x_873_, 2);
v_auxDeclNGen_877_ = lean_ctor_get(v___x_873_, 3);
v_traceState_878_ = lean_ctor_get(v___x_873_, 4);
v_cache_879_ = lean_ctor_get(v___x_873_, 5);
v_recordedDeps_880_ = lean_ctor_get(v___x_873_, 6);
v_messages_881_ = lean_ctor_get(v___x_873_, 7);
v_infoState_882_ = lean_ctor_get(v___x_873_, 8);
v_snapshotTasks_883_ = lean_ctor_get(v___x_873_, 9);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_894_ == 0)
{
v___x_885_ = v___x_873_;
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_snapshotTasks_883_);
lean_inc(v_infoState_882_);
lean_inc(v_messages_881_);
lean_inc(v_recordedDeps_880_);
lean_inc(v_cache_879_);
lean_inc(v_traceState_878_);
lean_inc(v_auxDeclNGen_877_);
lean_inc(v_ngen_876_);
lean_inc(v_nextMacroScope_875_);
lean_inc(v_env_874_);
lean_dec(v___x_873_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = lean_box(0);
v___x_888_ = l_Lean_MessageLog_add(v___x_872_, v_messages_881_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 7, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_env_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_nextMacroScope_875_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_ngen_876_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_auxDeclNGen_877_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_traceState_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 5, v_cache_879_);
lean_ctor_set(v_reuseFailAlloc_893_, 6, v_recordedDeps_880_);
lean_ctor_set(v_reuseFailAlloc_893_, 7, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_893_, 8, v_infoState_882_);
lean_ctor_set(v_reuseFailAlloc_893_, 9, v_snapshotTasks_883_);
v___x_890_ = v_reuseFailAlloc_893_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_st_ref_put(v___y_867_, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_887_);
return v___x_892_;
}
}
}
v___jp_895_:
{
lean_object* v_fileName_904_; lean_object* v_fileMap_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_921_; 
v_fileName_904_ = lean_ctor_get(v___y_902_, 0);
v_fileMap_905_ = lean_ctor_get(v___y_902_, 1);
v___x_906_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_850_);
v___x_907_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v___x_906_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_921_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc_ref_n(v_fileMap_905_, 2);
v___x_912_ = l_Lean_FileMap_toPosition(v_fileMap_905_, v___y_899_);
lean_dec(v___y_899_);
v___x_913_ = l_Lean_FileMap_toPosition(v_fileMap_905_, v___y_903_);
lean_dec(v___y_903_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
if (v___y_898_ == 0)
{
lean_del_object(v___x_910_);
lean_dec_ref(v___y_896_);
v___y_859_ = v___x_915_;
v___y_860_ = v_a_908_;
v___y_861_ = v___x_914_;
v___y_862_ = v___y_900_;
v___y_863_ = v___y_901_;
v___y_864_ = v___x_912_;
v___y_865_ = v_fileName_904_;
v_toCold_866_ = v___y_897_;
v___y_867_ = v___y_856_;
goto v___jp_858_;
}
else
{
uint8_t v___x_916_; 
lean_inc(v_a_908_);
v___x_916_ = l_Lean_MessageData_hasTag(v___y_896_, v_a_908_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_919_; 
lean_dec_ref_known(v___x_914_, 1);
lean_dec_ref(v___x_912_);
lean_dec(v_a_908_);
v___x_917_ = lean_box(0);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_917_);
v___x_919_ = v___x_910_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
else
{
lean_del_object(v___x_910_);
v___y_859_ = v___x_915_;
v___y_860_ = v_a_908_;
v___y_861_ = v___x_914_;
v___y_862_ = v___y_900_;
v___y_863_ = v___y_901_;
v___y_864_ = v___x_912_;
v___y_865_ = v_fileName_904_;
v_toCold_866_ = v___y_897_;
v___y_867_ = v___y_856_;
goto v___jp_858_;
}
}
}
}
v___jp_922_:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Syntax_getTailPos_x3f(v___y_927_, v___y_926_);
lean_dec(v___y_927_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_inc(v___y_929_);
v___y_896_ = v___y_924_;
v___y_897_ = v___y_925_;
v___y_898_ = v___y_923_;
v___y_899_ = v___y_929_;
v___y_900_ = v___y_926_;
v___y_901_ = v___y_928_;
v___y_902_ = v___y_925_;
v___y_903_ = v___y_929_;
goto v___jp_895_;
}
else
{
lean_object* v_val_931_; 
v_val_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_931_);
lean_dec_ref_known(v___x_930_, 1);
v___y_896_ = v___y_924_;
v___y_897_ = v___y_925_;
v___y_898_ = v___y_923_;
v___y_899_ = v___y_929_;
v___y_900_ = v___y_926_;
v___y_901_ = v___y_928_;
v___y_902_ = v___y_925_;
v___y_903_ = v_val_931_;
goto v___jp_895_;
}
}
v___jp_932_:
{
lean_object* v_toCold_936_; lean_object* v_ref_937_; uint8_t v_suppressElabErrors_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___f_941_; lean_object* v_ref_942_; lean_object* v___x_943_; 
v_toCold_936_ = lean_ctor_get(v___y_855_, 0);
v_ref_937_ = lean_ctor_get(v___y_855_, 2);
v_suppressElabErrors_938_ = lean_ctor_get_uint8(v___y_855_, sizeof(void*)*3 + 2);
v___x_939_ = lean_box(v_suppressElabErrors_938_);
v___x_940_ = lean_box(v___y_933_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_941_, 0, v___x_939_);
lean_closure_set(v___f_941_, 1, v___x_940_);
v_ref_942_ = l_Lean_replaceRef(v_ref_849_, v_ref_937_);
v___x_943_ = l_Lean_Syntax_getPos_x3f(v_ref_942_, v___y_934_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___y_923_ = v_suppressElabErrors_938_;
v___y_924_ = v___f_941_;
v___y_925_ = v_toCold_936_;
v___y_926_ = v___y_934_;
v___y_927_ = v_ref_942_;
v___y_928_ = v___y_935_;
v___y_929_ = v___x_944_;
goto v___jp_922_;
}
else
{
lean_object* v_val_945_; 
v_val_945_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v___x_943_, 1);
v___y_923_ = v_suppressElabErrors_938_;
v___y_924_ = v___f_941_;
v___y_925_ = v_toCold_936_;
v___y_926_ = v___y_934_;
v___y_927_ = v_ref_942_;
v___y_928_ = v___y_935_;
v___y_929_ = v_val_945_;
goto v___jp_922_;
}
}
v___jp_947_:
{
if (v___y_950_ == 0)
{
v___y_933_ = v___y_948_;
v___y_934_ = v___y_949_;
v___y_935_ = v_severity_851_;
goto v___jp_932_;
}
else
{
v___y_933_ = v___y_948_;
v___y_934_ = v___y_949_;
v___y_935_ = v___x_946_;
goto v___jp_932_;
}
}
v___jp_951_:
{
if (v___y_952_ == 0)
{
uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_953_ = 1;
v___x_954_ = l_Lean_instBEqMessageSeverity_beq(v_severity_851_, v___x_953_);
if (v___x_954_ == 0)
{
v___y_948_ = v___y_952_;
v___y_949_ = v___y_952_;
v___y_950_ = v___x_954_;
goto v___jp_947_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_955_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_855_);
v___x_956_ = l_Lean_warningAsError;
v___x_957_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v___x_955_, v___x_956_);
lean_dec_ref(v___x_955_);
v___y_948_ = v___y_952_;
v___y_949_ = v___y_952_;
v___y_950_ = v___x_957_;
goto v___jp_947_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec_ref(v_msgData_850_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_ref_962_, lean_object* v_msgData_963_, lean_object* v_severity_964_, lean_object* v_isSilent_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v_severity_boxed_971_; uint8_t v_isSilent_boxed_972_; lean_object* v_res_973_; 
v_severity_boxed_971_ = lean_unbox(v_severity_964_);
v_isSilent_boxed_972_ = lean_unbox(v_isSilent_965_);
v_res_973_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_962_, v_msgData_963_, v_severity_boxed_971_, v_isSilent_boxed_972_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v_ref_962_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_msgData_974_, uint8_t v_severity_975_, uint8_t v_isSilent_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_ref_982_; lean_object* v___x_983_; 
v_ref_982_ = lean_ctor_get(v___y_979_, 2);
v___x_983_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_982_, v_msgData_974_, v_severity_975_, v_isSilent_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_msgData_984_, lean_object* v_severity_985_, lean_object* v_isSilent_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v_severity_boxed_992_; uint8_t v_isSilent_boxed_993_; lean_object* v_res_994_; 
v_severity_boxed_992_ = lean_unbox(v_severity_985_);
v_isSilent_boxed_993_ = lean_unbox(v_isSilent_986_);
v_res_994_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_984_, v_severity_boxed_992_, v_isSilent_boxed_993_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(lean_object* v_msgData_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
uint8_t v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = 1;
v___x_1002_ = 0;
v___x_1003_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_995_, v___x_1001_, v___x_1002_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3___boxed(lean_object* v_msgData_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v_msgData_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__7_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t v_builtin_1023_, lean_object* v_decl_1024_, uint8_t v___x_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_stx_1028_, uint8_t v_kind_1029_, lean_object* v_name_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1028_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1138_) == 0)
{
uint8_t v___x_1139_; uint8_t v___x_1140_; 
lean_dec_ref_known(v___x_1138_, 1);
v___x_1139_ = 0;
v___x_1140_ = l_Lean_instBEqAttributeKind_beq(v_kind_1029_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_decl_1024_);
v___x_1141_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_1030_, v_kind_1029_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1141_;
}
else
{
lean_dec(v_name_1030_);
goto v___jp_1100_;
}
}
else
{
lean_dec(v_name_1030_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_decl_1024_);
return v___x_1138_;
}
v___jp_1036_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_st_ref_get(v___y_1043_);
if (v_builtin_1023_ == 0)
{
lean_object* v_env_1045_; uint64_t v_javascriptHash_1046_; lean_object* v___x_1047_; lean_object* v_toEnvExtension_1048_; lean_object* v_asyncMode_1049_; uint8_t v_logWrites_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; 
lean_dec(v___y_1037_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
v_env_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc_ref(v_env_1045_);
lean_dec(v___x_1044_);
v_javascriptHash_1046_ = lean_ctor_get_uint64(v___y_1038_, sizeof(void*)*1);
lean_dec_ref(v___y_1038_);
v___x_1047_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1048_ = lean_ctor_get(v___x_1047_, 0);
v_asyncMode_1049_ = lean_ctor_get(v_toEnvExtension_1048_, 2);
v_logWrites_1050_ = lean_ctor_get_uint8(v_toEnvExtension_1048_, sizeof(void*)*6);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_decl_1024_);
lean_ctor_set(v___x_1051_, 1, v___y_1039_);
v___x_1052_ = lean_box_uint64(v_javascriptHash_1046_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_1051_);
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1054_, 0, v___x_1047_);
lean_closure_set(v___f_1054_, 1, v___x_1053_);
v___x_1055_ = lean_box(0);
if (v_logWrites_1050_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_inc_ref(v_toEnvExtension_1048_);
v___x_1056_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1048_, v_env_1045_, v___f_1054_, v_asyncMode_1049_, v___x_1055_, v___x_1025_);
v___x_1057_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v___x_1056_, v___y_1041_, v___y_1043_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_inc_ref_n(v_toEnvExtension_1048_, 2);
v___x_1058_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1048_, v_env_1045_);
lean_dec_ref(v_env_1045_);
v___x_1059_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1048_, v___x_1058_, v___f_1054_, v_asyncMode_1049_, v___x_1055_, v___x_1025_);
v___x_1060_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v___x_1059_, v___y_1041_, v___y_1043_);
return v___x_1060_;
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v___x_1044_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_n(v_decl_1024_, 2);
v___x_1061_ = l_Lean_mkConst(v_decl_1024_, v___y_1037_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1063_ = l_Lean_Name_mkStr3(v___x_1026_, v___x_1027_, v___x_1062_);
v___x_1064_ = l_Lean_mkConst(v___x_1063_, v___y_1037_);
v___x_1065_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_1024_);
v___x_1066_ = l_Lean_mkAppB(v___x_1064_, v___x_1065_, v___x_1061_);
v___x_1067_ = l_Lean_declareBuiltin(v_decl_1024_, v___x_1066_, v___y_1042_, v___y_1043_);
return v___x_1067_;
}
}
v___jp_1068_:
{
lean_object* v___x_1077_; lean_object* v_toEnvExtension_1078_; lean_object* v_asyncMode_1079_; uint64_t v_javascriptHash_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1077_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1078_ = lean_ctor_get(v___x_1077_, 0);
v_asyncMode_1079_ = lean_ctor_get(v_toEnvExtension_1078_, 2);
v_javascriptHash_1080_ = lean_ctor_get_uint64(v___y_1071_, sizeof(void*)*1);
v___x_1081_ = lean_box(1);
v___x_1082_ = lean_box(0);
v___x_1083_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1081_, v___x_1077_, v___y_1069_, v_asyncMode_1079_, v___x_1082_);
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1083_, v_javascriptHash_1080_);
lean_dec(v___x_1083_);
if (lean_obj_tag(v___x_1084_) == 1)
{
lean_object* v_val_1085_; lean_object* v_fst_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1098_; 
v_val_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v_fst_1086_ = lean_ctor_get(v_val_1085_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_val_1085_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_val_1085_, 1);
lean_dec(v_unused_1099_);
v___x_1088_ = v_val_1085_;
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_fst_1086_);
lean_dec(v_val_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1091_ = l_Lean_MessageData_ofConstName(v_fst_1086_, v___x_1025_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 7);
lean_ctor_set(v___x_1088_, 1, v___x_1091_);
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v___x_1095_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref_known(v___x_1096_, 1);
v___y_1037_ = v___y_1070_;
v___y_1038_ = v___y_1071_;
v___y_1039_ = v___y_1072_;
v___y_1040_ = v___y_1073_;
v___y_1041_ = v___y_1074_;
v___y_1042_ = v___y_1075_;
v___y_1043_ = v___y_1076_;
goto v___jp_1036_;
}
else
{
lean_dec_ref(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_decl_1024_);
return v___x_1096_;
}
}
}
}
else
{
lean_dec(v___x_1084_);
v___y_1037_ = v___y_1070_;
v___y_1038_ = v___y_1071_;
v___y_1039_ = v___y_1072_;
v___y_1040_ = v___y_1073_;
v___y_1041_ = v___y_1074_;
v___y_1042_ = v___y_1075_;
v___y_1043_ = v___y_1076_;
goto v___jp_1036_;
}
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1102_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
lean_inc_ref(v___x_1027_);
lean_inc_ref(v___x_1026_);
v___x_1103_ = l_Lean_Name_mkStr4(v___x_1026_, v___x_1027_, v___x_1101_, v___x_1102_);
v___x_1104_ = lean_box(0);
lean_inc(v_decl_1024_);
v___x_1105_ = l_Lean_Expr_const___override(v_decl_1024_, v___x_1104_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1106_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1105_);
v___x_1109_ = l_Lean_Meta_mkAppM(v___x_1103_, v___x_1108_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_n(v_a_1110_, 2);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_1110_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = lean_st_ref_get(v___y_1034_);
if (v_builtin_1023_ == 0)
{
lean_object* v_env_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint64_t v_javascriptHash_1117_; lean_object* v___x_1118_; 
v_env_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1116_ = lean_st_ref_get(v___x_1115_);
v_javascriptHash_1117_ = lean_ctor_get_uint64(v_a_1112_, sizeof(void*)*1);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1116_, v_javascriptHash_1117_);
lean_dec(v___x_1116_);
if (lean_obj_tag(v___x_1118_) == 1)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref_known(v___x_1118_, 1);
v___x_1119_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1120_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v___x_1119_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_dec_ref_known(v___x_1120_, 1);
v___y_1069_ = v_env_1114_;
v___y_1070_ = v___x_1104_;
v___y_1071_ = v_a_1112_;
v___y_1072_ = v_a_1110_;
v___y_1073_ = v___y_1031_;
v___y_1074_ = v___y_1032_;
v___y_1075_ = v___y_1033_;
v___y_1076_ = v___y_1034_;
goto v___jp_1068_;
}
else
{
lean_dec_ref(v_env_1114_);
lean_dec(v_a_1112_);
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_decl_1024_);
return v___x_1120_;
}
}
else
{
lean_dec(v___x_1118_);
v___y_1069_ = v_env_1114_;
v___y_1070_ = v___x_1104_;
v___y_1071_ = v_a_1112_;
v___y_1072_ = v_a_1110_;
v___y_1073_ = v___y_1031_;
v___y_1074_ = v___y_1032_;
v___y_1075_ = v___y_1033_;
v___y_1076_ = v___y_1034_;
goto v___jp_1068_;
}
}
else
{
lean_object* v_env_1121_; 
v_env_1121_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1121_);
lean_dec(v___x_1113_);
v___y_1069_ = v_env_1121_;
v___y_1070_ = v___x_1104_;
v___y_1071_ = v_a_1112_;
v___y_1072_ = v_a_1110_;
v___y_1073_ = v___y_1031_;
v___y_1074_ = v___y_1032_;
v___y_1075_ = v___y_1033_;
v___y_1076_ = v___y_1034_;
goto v___jp_1068_;
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_decl_1024_);
v_a_1122_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1111_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1111_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_decl_1024_);
v_a_1130_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1109_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1109_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_builtin_1142_, lean_object* v_decl_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v_stx_1147_, lean_object* v_kind_1148_, lean_object* v_name_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v_builtin_boxed_1155_; uint8_t v___x_11531__boxed_1156_; uint8_t v_kind_boxed_1157_; lean_object* v_res_1158_; 
v_builtin_boxed_1155_ = lean_unbox(v_builtin_1142_);
v___x_11531__boxed_1156_ = lean_unbox(v___x_1144_);
v_kind_boxed_1157_ = lean_unbox(v_kind_1148_);
v_res_1158_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_boxed_1155_, v_decl_1143_, v___x_11531__boxed_1156_, v___x_1145_, v___x_1146_, v_stx_1147_, v_kind_boxed_1157_, v_name_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object* v___y_1159_, uint8_t v_isExporting_1160_, lean_object* v___x_1161_, lean_object* v___y_1162_, lean_object* v___x_1163_, lean_object* v_a_x3f_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v_env_1167_; lean_object* v_nextMacroScope_1168_; lean_object* v_ngen_1169_; lean_object* v_auxDeclNGen_1170_; lean_object* v_traceState_1171_; lean_object* v_recordedDeps_1172_; lean_object* v_messages_1173_; lean_object* v_infoState_1174_; lean_object* v_snapshotTasks_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1200_; 
v___x_1166_ = lean_st_ref_take(v___y_1159_);
v_env_1167_ = lean_ctor_get(v___x_1166_, 0);
v_nextMacroScope_1168_ = lean_ctor_get(v___x_1166_, 1);
v_ngen_1169_ = lean_ctor_get(v___x_1166_, 2);
v_auxDeclNGen_1170_ = lean_ctor_get(v___x_1166_, 3);
v_traceState_1171_ = lean_ctor_get(v___x_1166_, 4);
v_recordedDeps_1172_ = lean_ctor_get(v___x_1166_, 6);
v_messages_1173_ = lean_ctor_get(v___x_1166_, 7);
v_infoState_1174_ = lean_ctor_get(v___x_1166_, 8);
v_snapshotTasks_1175_ = lean_ctor_get(v___x_1166_, 9);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1166_, 5);
lean_dec(v_unused_1201_);
v___x_1177_ = v___x_1166_;
v_isShared_1178_ = v_isSharedCheck_1200_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snapshotTasks_1175_);
lean_inc(v_infoState_1174_);
lean_inc(v_messages_1173_);
lean_inc(v_recordedDeps_1172_);
lean_inc(v_traceState_1171_);
lean_inc(v_auxDeclNGen_1170_);
lean_inc(v_ngen_1169_);
lean_inc(v_nextMacroScope_1168_);
lean_inc(v_env_1167_);
lean_dec(v___x_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1200_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_Environment_setExporting(v_env_1167_, v_isExporting_1160_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 5, v___x_1161_);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_nextMacroScope_1168_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_ngen_1169_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_auxDeclNGen_1170_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v_traceState_1171_);
lean_ctor_set(v_reuseFailAlloc_1199_, 5, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1199_, 6, v_recordedDeps_1172_);
lean_ctor_set(v_reuseFailAlloc_1199_, 7, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1199_, 8, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1199_, 9, v_snapshotTasks_1175_);
v___x_1181_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_mctx_1184_; lean_object* v_zetaDeltaFVarIds_1185_; lean_object* v_postponed_1186_; lean_object* v_diag_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1197_; 
v___x_1182_ = lean_st_ref_put(v___y_1159_, v___x_1181_);
v___x_1183_ = lean_st_ref_take(v___y_1162_);
v_mctx_1184_ = lean_ctor_get(v___x_1183_, 0);
v_zetaDeltaFVarIds_1185_ = lean_ctor_get(v___x_1183_, 2);
v_postponed_1186_ = lean_ctor_get(v___x_1183_, 3);
v_diag_1187_ = lean_ctor_get(v___x_1183_, 4);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1183_, 1);
lean_dec(v_unused_1198_);
v___x_1189_ = v___x_1183_;
v_isShared_1190_ = v_isSharedCheck_1197_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_diag_1187_);
lean_inc(v_postponed_1186_);
lean_inc(v_zetaDeltaFVarIds_1185_);
lean_inc(v_mctx_1184_);
lean_dec(v___x_1183_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1197_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1163_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_mctx_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_zetaDeltaFVarIds_1185_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_postponed_1186_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_diag_1187_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_st_ref_put(v___y_1162_, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1191_);
return v___x_1195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object* v___y_1202_, lean_object* v_isExporting_1203_, lean_object* v___x_1204_, lean_object* v___y_1205_, lean_object* v___x_1206_, lean_object* v_a_x3f_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_isExporting_boxed_1209_; lean_object* v_res_1210_; 
v_isExporting_boxed_1209_ = lean_unbox(v_isExporting_1203_);
v_res_1210_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1202_, v_isExporting_boxed_1209_, v___x_1204_, v___y_1205_, v___x_1206_, v_a_x3f_1207_);
lean_dec(v_a_x3f_1207_);
lean_dec(v___y_1205_);
lean_dec(v___y_1202_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object* v_x_1211_, uint8_t v_isExporting_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_env_1219_; lean_object* v___x_1220_; uint8_t v_isModule_1221_; 
v___x_1218_ = lean_st_ref_get(v___y_1216_);
v_env_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref(v_env_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Lean_Environment_header(v_env_1219_);
v_isModule_1221_ = lean_ctor_get_uint8(v___x_1220_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1220_);
if (v_isModule_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v_env_1219_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1222_ = lean_apply_5(v_x_1211_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
return v___x_1222_;
}
else
{
uint8_t v_isExporting_1223_; 
v_isExporting_1223_ = lean_ctor_get_uint8(v_env_1219_, sizeof(void*)*13);
lean_dec_ref(v_env_1219_);
if (v_isExporting_1212_ == 0)
{
if (v_isExporting_1223_ == 0)
{
lean_object* v___x_1290_; 
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1290_ = lean_apply_5(v_x_1211_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
return v___x_1290_;
}
else
{
goto v___jp_1224_;
}
}
else
{
if (v_isExporting_1223_ == 0)
{
goto v___jp_1224_;
}
else
{
lean_object* v___x_1291_; 
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1291_ = lean_apply_5(v_x_1211_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
return v___x_1291_;
}
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v_env_1226_; lean_object* v_nextMacroScope_1227_; lean_object* v_ngen_1228_; lean_object* v_auxDeclNGen_1229_; lean_object* v_traceState_1230_; lean_object* v_recordedDeps_1231_; lean_object* v_messages_1232_; lean_object* v_infoState_1233_; lean_object* v_snapshotTasks_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1288_; 
v___x_1225_ = lean_st_ref_take(v___y_1216_);
v_env_1226_ = lean_ctor_get(v___x_1225_, 0);
v_nextMacroScope_1227_ = lean_ctor_get(v___x_1225_, 1);
v_ngen_1228_ = lean_ctor_get(v___x_1225_, 2);
v_auxDeclNGen_1229_ = lean_ctor_get(v___x_1225_, 3);
v_traceState_1230_ = lean_ctor_get(v___x_1225_, 4);
v_recordedDeps_1231_ = lean_ctor_get(v___x_1225_, 6);
v_messages_1232_ = lean_ctor_get(v___x_1225_, 7);
v_infoState_1233_ = lean_ctor_get(v___x_1225_, 8);
v_snapshotTasks_1234_ = lean_ctor_get(v___x_1225_, 9);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1225_, 5);
lean_dec(v_unused_1289_);
v___x_1236_ = v___x_1225_;
v_isShared_1237_ = v_isSharedCheck_1288_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snapshotTasks_1234_);
lean_inc(v_infoState_1233_);
lean_inc(v_messages_1232_);
lean_inc(v_recordedDeps_1231_);
lean_inc(v_traceState_1230_);
lean_inc(v_auxDeclNGen_1229_);
lean_inc(v_ngen_1228_);
lean_inc(v_nextMacroScope_1227_);
lean_inc(v_env_1226_);
lean_dec(v___x_1225_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1288_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = l_Lean_Environment_setExporting(v_env_1226_, v_isExporting_1212_);
v___x_1239_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 5, v___x_1239_);
lean_ctor_set(v___x_1236_, 0, v___x_1238_);
v___x_1241_ = v___x_1236_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_nextMacroScope_1227_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_ngen_1228_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_auxDeclNGen_1229_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_traceState_1230_);
lean_ctor_set(v_reuseFailAlloc_1287_, 5, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1287_, 6, v_recordedDeps_1231_);
lean_ctor_set(v_reuseFailAlloc_1287_, 7, v_messages_1232_);
lean_ctor_set(v_reuseFailAlloc_1287_, 8, v_infoState_1233_);
lean_ctor_set(v_reuseFailAlloc_1287_, 9, v_snapshotTasks_1234_);
v___x_1241_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_mctx_1244_; lean_object* v_zetaDeltaFVarIds_1245_; lean_object* v_postponed_1246_; lean_object* v_diag_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1285_; 
v___x_1242_ = lean_st_ref_put(v___y_1216_, v___x_1241_);
v___x_1243_ = lean_st_ref_take(v___y_1214_);
v_mctx_1244_ = lean_ctor_get(v___x_1243_, 0);
v_zetaDeltaFVarIds_1245_ = lean_ctor_get(v___x_1243_, 2);
v_postponed_1246_ = lean_ctor_get(v___x_1243_, 3);
v_diag_1247_ = lean_ctor_get(v___x_1243_, 4);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1243_, 1);
lean_dec(v_unused_1286_);
v___x_1249_ = v___x_1243_;
v_isShared_1250_ = v_isSharedCheck_1285_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_diag_1247_);
lean_inc(v_postponed_1246_);
lean_inc(v_zetaDeltaFVarIds_1245_);
lean_inc(v_mctx_1244_);
lean_dec(v___x_1243_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1285_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_mctx_1244_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_zetaDeltaFVarIds_1245_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_postponed_1246_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_diag_1247_);
v___x_1253_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v_r_1255_; 
v___x_1254_ = lean_st_ref_put(v___y_1214_, v___x_1253_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v_r_1255_ = lean_apply_5(v_x_1211_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
if (lean_obj_tag(v_r_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1272_; 
v_a_1256_ = lean_ctor_get(v_r_1255_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_r_1255_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1258_ = v_r_1255_;
v_isShared_1259_ = v_isSharedCheck_1272_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v_r_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1272_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
lean_inc(v_a_1256_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 1);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v___x_1262_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1216_, v_isExporting_1223_, v___x_1239_, v___y_1214_, v___x_1251_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1262_, 0);
lean_dec(v_unused_1270_);
v___x_1264_ = v___x_1262_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_dec(v___x_1262_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_a_1256_);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1256_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_a_1273_ = lean_ctor_get(v_r_1255_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v_r_1255_, 1);
v___x_1274_ = lean_box(0);
v___x_1275_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1216_, v_isExporting_1223_, v___x_1239_, v___y_1214_, v___x_1251_, v___x_1274_);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1283_);
v___x_1277_ = v___x_1275_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v___x_1275_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
lean_ctor_set(v___x_1277_, 0, v_a_1273_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1273_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object* v_x_1292_, lean_object* v_isExporting_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_isExporting_boxed_1299_; lean_object* v_res_1300_; 
v_isExporting_boxed_1299_ = lean_unbox(v_isExporting_1293_);
v_res_1300_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1292_, v_isExporting_boxed_1299_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(lean_object* v_x_1301_, uint8_t v_when_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
if (v_when_1302_ == 0)
{
lean_object* v___x_1308_; 
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
v___x_1308_ = lean_apply_5(v_x_1301_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
return v___x_1308_;
}
else
{
uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = 0;
v___x_1310_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1301_, v___x_1309_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_x_1311_, lean_object* v_when_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_when_boxed_1318_; lean_object* v_res_1319_; 
v_when_boxed_1318_ = lean_unbox(v_when_1312_);
v_res_1319_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1311_, v_when_boxed_1318_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1319_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1322_ = lean_box(1);
v___x_1323_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1324_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
lean_ctor_set(v___x_1325_, 2, v___x_1322_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1329_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
lean_ctor_set(v___x_1331_, 3, v___x_1330_);
lean_ctor_set(v___x_1331_, 4, v___x_1329_);
lean_ctor_set(v___x_1331_, 5, v___x_1329_);
lean_ctor_set(v___x_1331_, 6, v___x_1329_);
lean_ctor_set(v___x_1331_, 7, v___x_1329_);
lean_ctor_set(v___x_1331_, 8, v___x_1329_);
lean_ctor_set(v___x_1331_, 9, v___x_1329_);
lean_ctor_set(v___x_1331_, 10, v___x_1329_);
lean_ctor_set(v___x_1331_, 11, v___x_1328_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1333_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
lean_ctor_set(v___x_1333_, 2, v___x_1332_);
lean_ctor_set(v___x_1333_, 3, v___x_1332_);
lean_ctor_set(v___x_1333_, 4, v___x_1332_);
lean_ctor_set(v___x_1333_, 5, v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
lean_ctor_set(v___x_1335_, 3, v___x_1334_);
lean_ctor_set(v___x_1335_, 4, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t v_builtin_1336_, uint8_t v___x_1337_, lean_object* v___x_1338_, lean_object* v___x_1339_, lean_object* v_name_1340_, lean_object* v___x_1341_, lean_object* v_decl_1342_, lean_object* v_stx_1343_, uint8_t v_kind_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; uint64_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1348_ = lean_box(v_builtin_1336_);
v___x_1349_ = lean_box(v___x_1337_);
v___x_1350_ = lean_box(v_kind_1344_);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 13, 8);
lean_closure_set(v___f_1351_, 0, v___x_1348_);
lean_closure_set(v___f_1351_, 1, v_decl_1342_);
lean_closure_set(v___f_1351_, 2, v___x_1349_);
lean_closure_set(v___f_1351_, 3, v___x_1338_);
lean_closure_set(v___f_1351_, 4, v___x_1339_);
lean_closure_set(v___f_1351_, 5, v_stx_1343_);
lean_closure_set(v___f_1351_, 6, v___x_1350_);
lean_closure_set(v___f_1351_, 7, v_name_1340_);
v___x_1352_ = 0;
v___x_1353_ = 1;
v___x_1354_ = 0;
v___x_1355_ = 2;
v___x_1356_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1356_, 0, v___x_1352_);
lean_ctor_set_uint8(v___x_1356_, 1, v___x_1352_);
lean_ctor_set_uint8(v___x_1356_, 2, v___x_1352_);
lean_ctor_set_uint8(v___x_1356_, 3, v___x_1352_);
lean_ctor_set_uint8(v___x_1356_, 4, v___x_1352_);
lean_ctor_set_uint8(v___x_1356_, 5, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 6, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 7, v___x_1352_);
lean_ctor_set_uint8(v___x_1356_, 8, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 9, v___x_1353_);
lean_ctor_set_uint8(v___x_1356_, 10, v___x_1354_);
lean_ctor_set_uint8(v___x_1356_, 11, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 12, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 13, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 14, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, 15, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 16, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 17, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 18, v___x_1337_);
lean_ctor_set_uint8(v___x_1356_, 19, v___x_1352_);
v___x_1357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set_uint64(v___x_1358_, sizeof(void*)*1, v___x_1357_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1361_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1362_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1363_ = lean_box(0);
lean_inc(v___x_1341_);
v___x_1364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1364_, 0, v___x_1358_);
lean_ctor_set(v___x_1364_, 1, v___x_1341_);
lean_ctor_set(v___x_1364_, 2, v___x_1361_);
lean_ctor_set(v___x_1364_, 3, v___x_1362_);
lean_ctor_set(v___x_1364_, 4, v___x_1363_);
lean_ctor_set(v___x_1364_, 5, v___x_1359_);
lean_ctor_set(v___x_1364_, 6, v___x_1363_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*7, v___x_1352_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*7 + 1, v___x_1352_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*7 + 2, v___x_1352_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*7 + 3, v___x_1337_);
v___x_1365_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1366_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1367_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1365_);
lean_ctor_set(v___x_1368_, 1, v___x_1366_);
lean_ctor_set(v___x_1368_, 2, v___x_1341_);
lean_ctor_set(v___x_1368_, 3, v___x_1360_);
lean_ctor_set(v___x_1368_, 4, v___x_1367_);
v___x_1369_ = lean_st_mk_ref(v___x_1368_);
v___x_1370_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v___f_1351_, v___x_1337_, v___x_1364_, v___x_1369_, v___y_1345_, v___y_1346_);
lean_dec_ref_known(v___x_1364_, 7);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_st_ref_get(v___x_1369_);
lean_dec(v___x_1369_);
lean_dec(v___x_1375_);
if (v_isShared_1374_ == 0)
{
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1371_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_dec(v___x_1369_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_builtin_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v___x_1383_, lean_object* v_name_1384_, lean_object* v___x_1385_, lean_object* v_decl_1386_, lean_object* v_stx_1387_, lean_object* v_kind_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_builtin_boxed_1392_; uint8_t v___x_12076__boxed_1393_; uint8_t v_kind_boxed_1394_; lean_object* v_res_1395_; 
v_builtin_boxed_1392_ = lean_unbox(v_builtin_1380_);
v___x_12076__boxed_1393_ = lean_unbox(v___x_1381_);
v_kind_boxed_1394_ = lean_unbox(v_kind_1388_);
v_res_1395_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_boxed_1392_, v___x_12076__boxed_1393_, v___x_1382_, v___x_1383_, v_name_1384_, v___x_1385_, v_decl_1386_, v_stx_1387_, v_kind_boxed_1394_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v___x_1403_, uint8_t v_builtin_1404_, lean_object* v_name_1405_){
_start:
{
lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___y_1416_; 
lean_inc_n(v_name_1405_, 2);
v___f_1407_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1407_, 0, v_name_1405_);
v___x_1408_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0));
v___x_1409_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1));
v___x_1410_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1411_ = 1;
v___x_1412_ = lean_box(v_builtin_1404_);
v___x_1413_ = lean_box(v___x_1411_);
v___f_1414_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1414_, 0, v___x_1412_);
lean_closure_set(v___f_1414_, 1, v___x_1413_);
lean_closure_set(v___f_1414_, 2, v___x_1408_);
lean_closure_set(v___f_1414_, 3, v___x_1409_);
lean_closure_set(v___f_1414_, 4, v_name_1405_);
lean_closure_set(v___f_1414_, 5, v___x_1403_);
if (v_builtin_1404_ == 0)
{
lean_object* v___x_1439_; 
v___x_1439_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___y_1416_ = v___x_1439_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___y_1416_ = v___x_1440_;
goto v___jp_1415_;
}
v___jp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v_impl_1421_; lean_object* v___x_1422_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
lean_inc_ref(v___y_1416_);
v___x_1418_ = lean_string_append(v___y_1416_, v___x_1417_);
v___x_1419_ = 1;
v___x_1420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1420_, 0, v___x_1410_);
lean_ctor_set(v___x_1420_, 1, v_name_1405_);
lean_ctor_set(v___x_1420_, 2, v___x_1418_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*3, v___x_1419_);
v_impl_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_impl_1421_, 0, v___x_1420_);
lean_ctor_set(v_impl_1421_, 1, v___f_1414_);
lean_ctor_set(v_impl_1421_, 2, v___f_1407_);
lean_inc_ref(v_impl_1421_);
v___x_1422_ = l_Lean_registerBuiltinAttribute(v_impl_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_impl_1421_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_impl_1421_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref_known(v_impl_1421_, 3);
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1422_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1422_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v___x_1441_, lean_object* v_builtin_1442_, lean_object* v_name_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v_builtin_boxed_1445_; lean_object* v_res_1446_; 
v_builtin_boxed_1445_ = lean_unbox(v_builtin_1442_);
v_res_1446_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1441_, v_builtin_boxed_1445_, v_name_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = lean_box(1);
v___x_1455_ = 1;
v___x_1456_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1457_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1454_, v___x_1455_, v___x_1456_);
if (lean_obj_tag(v___x_1457_) == 0)
{
uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec_ref_known(v___x_1457_, 1);
v___x_1458_ = 0;
v___x_1459_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1460_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1454_, v___x_1458_, v___x_1459_);
return v___x_1460_;
}
else
{
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_();
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1463_, lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_1464_, v___y_1465_, v___y_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(v_00_u03b1_1469_, v_msg_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_1475_, lean_object* v_t_1476_, uint64_t v_k_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_1476_, v_k_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_1479_, lean_object* v_t_1480_, lean_object* v_k_1481_){
_start:
{
uint64_t v_k_boxed_1482_; lean_object* v_res_1483_; 
v_k_boxed_1482_ = lean_unbox_uint64(v_k_1481_);
lean_dec_ref(v_k_1481_);
v_res_1483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(v_00_u03b4_1479_, v_t_1480_, v_k_boxed_1482_);
lean_dec(v_t_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1484_, lean_object* v_name_1485_, uint8_t v_kind_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_1485_, v_kind_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_name_1494_, lean_object* v_kind_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_kind_boxed_1501_; lean_object* v_res_1502_; 
v_kind_boxed_1501_ = lean_unbox(v_kind_1495_);
v_res_1502_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(v_00_u03b1_1493_, v_name_1494_, v_kind_boxed_1501_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(lean_object* v_00_u03b1_1503_, lean_object* v_x_1504_, uint8_t v_isExporting_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1504_, v_isExporting_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object* v_00_u03b1_1512_, lean_object* v_x_1513_, lean_object* v_isExporting_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_isExporting_boxed_1520_; lean_object* v_res_1521_; 
v_isExporting_boxed_1520_ = lean_unbox(v_isExporting_1514_);
v_res_1521_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(v_00_u03b1_1512_, v_x_1513_, v_isExporting_boxed_1520_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1522_, lean_object* v_x_1523_, uint8_t v_when_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1523_, v_when_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_x_1532_, lean_object* v_when_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_when_boxed_1539_; lean_object* v_res_1540_; 
v_when_boxed_1539_ = lean_unbox(v_when_1533_);
v_res_1540_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(v_00_u03b1_1531_, v_x_1532_, v_when_boxed_1539_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1541_, lean_object* v_msg_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
if (lean_obj_tag(v_a_1557_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_array_to_list(v_a_1558_);
return v___x_1559_;
}
else
{
lean_object* v_head_1560_; lean_object* v_tail_1561_; lean_object* v___x_1562_; 
v_head_1560_ = lean_ctor_get(v_a_1557_, 0);
lean_inc(v_head_1560_);
v_tail_1561_ = lean_ctor_get(v_a_1557_, 1);
lean_inc(v_tail_1561_);
lean_dec_ref_known(v_a_1557_, 2);
v___x_1562_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1558_, v_head_1560_);
v_a_1557_ = v_tail_1561_;
v_a_1558_ = v___x_1562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object* v_x_1568_){
_start:
{
uint64_t v_hash_1569_; lean_object* v_pos_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_hash_1569_ = lean_ctor_get_uint64(v_x_1568_, sizeof(void*)*1);
v_pos_1570_ = lean_ctor_get(v_x_1568_, 0);
lean_inc_ref(v_pos_1570_);
lean_dec_ref(v_x_1568_);
v___x_1571_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
v___x_1572_ = lean_uint64_to_nat(v_hash_1569_);
v___x_1573_ = l_Lean_bignumToJson(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1578_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_1570_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1575_);
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___x_1575_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1576_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1584_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1582_, v___x_1583_);
v___x_1585_ = l_Lean_Json_mkObj(v___x_1584_);
lean_dec(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object* v_j_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = l_Lean_Json_getObjValD(v_j_1588_, v_k_1589_);
v___x_1591_ = l_Lean_UInt64_fromJson_x3f(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object* v_j_1592_, lean_object* v_k_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_j_1592_, v_k_1593_);
lean_dec_ref(v_k_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object* v_j_1595_, lean_object* v_k_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = l_Lean_Json_getObjValD(v_j_1595_, v_k_1596_);
v___x_1598_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object* v_j_1599_, lean_object* v_k_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_j_1599_, v_k_1600_);
lean_dec_ref(v_k_1600_);
return v_res_1601_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = 1;
v___x_1608_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1));
v___x_1609_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1608_, v___x_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1611_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2);
v___x_1612_ = lean_string_append(v___x_1611_, v___x_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = 1;
v___x_1616_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4));
v___x_1617_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5);
v___x_1619_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1620_ = lean_string_append(v___x_1619_, v___x_1618_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1623_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6);
v___x_1624_ = lean_string_append(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = 1;
v___x_1628_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9));
v___x_1629_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1628_, v___x_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10);
v___x_1631_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1632_ = lean_string_append(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1634_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11);
v___x_1635_ = lean_string_append(v___x_1634_, v___x_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object* v_json_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
lean_inc(v_json_1636_);
v___x_1638_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_json_1636_, v___x_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_json_1636_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1643_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8);
v___x_1644_ = lean_string_append(v___x_1643_, v_a_1639_);
lean_dec(v_a_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1644_);
v___x_1646_ = v___x_1641_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
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
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_json_1636_);
v_a_1649_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1638_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1638_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 0);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_a_1657_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1658_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1659_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_json_1636_, v___x_1658_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_a_1657_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1664_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12);
v___x_1665_ = lean_string_append(v___x_1664_, v_a_1660_);
lean_dec(v_a_1660_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_a_1657_);
v_a_1670_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1659_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1659_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 0);
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1687_; 
v_a_1678_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1680_ = v___x_1659_;
v_isShared_1681_ = v_isSharedCheck_1687_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1659_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1687_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; uint64_t v___x_1683_; lean_object* v___x_1685_; 
v___x_1682_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1682_, 0, v_a_1678_);
v___x_1683_ = lean_unbox_uint64(v_a_1657_);
lean_dec(v_a_1657_);
lean_ctor_set_uint64(v___x_1682_, sizeof(void*)*1, v___x_1683_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1682_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson(lean_object* v_x_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1694_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_x_1693_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_box(0);
v___x_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
v___x_1700_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1701_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1699_, v___x_1700_);
v___x_1702_ = l_Lean_Json_mkObj(v___x_1701_);
lean_dec(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(lean_object* v_j_1705_, lean_object* v_k_1706_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = l_Lean_Json_getObjValD(v_j_1705_, v_k_1706_);
v___x_1708_ = l_Lean_Json_getStr_x3f(v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0___boxed(lean_object* v_j_1709_, lean_object* v_k_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_j_1709_, v_k_1710_);
lean_dec_ref(v_k_1710_);
return v_res_1711_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = 1;
v___x_1718_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1));
v___x_1719_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1721_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2);
v___x_1722_ = lean_string_append(v___x_1721_, v___x_1720_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = 1;
v___x_1726_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4));
v___x_1727_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5);
v___x_1729_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3);
v___x_1730_ = lean_string_append(v___x_1729_, v___x_1728_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1732_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6);
v___x_1733_ = lean_string_append(v___x_1732_, v___x_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson(lean_object* v_json_1734_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1736_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_1734_, v___x_1735_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1746_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1741_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7);
v___x_1742_ = lean_string_append(v___x_1741_, v_a_1737_);
lean_dec(v_a_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1742_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1736_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1736_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 0);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
v_a_1755_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1736_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1736_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object* v___y_1765_){
_start:
{
lean_object* v_doc_1767_; lean_object* v___x_1768_; 
v_doc_1767_ = lean_ctor_get(v___y_1765_, 1);
lean_inc_ref(v_doc_1767_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_doc_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1769_);
lean_dec_ref(v___y_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t v_k_1772_, lean_object* v_t_1773_){
_start:
{
if (lean_obj_tag(v_t_1773_) == 0)
{
lean_object* v_k_1774_; lean_object* v_l_1775_; lean_object* v_r_1776_; uint64_t v___x_1777_; uint8_t v___x_1778_; 
v_k_1774_ = lean_ctor_get(v_t_1773_, 1);
v_l_1775_ = lean_ctor_get(v_t_1773_, 3);
v_r_1776_ = lean_ctor_get(v_t_1773_, 4);
v___x_1777_ = lean_unbox_uint64(v_k_1774_);
v___x_1778_ = lean_uint64_dec_lt(v_k_1772_, v___x_1777_);
if (v___x_1778_ == 0)
{
uint64_t v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = lean_unbox_uint64(v_k_1774_);
v___x_1780_ = lean_uint64_dec_eq(v_k_1772_, v___x_1779_);
if (v___x_1780_ == 0)
{
v_t_1773_ = v_r_1776_;
goto _start;
}
else
{
return v___x_1780_;
}
}
else
{
v_t_1773_ = v_l_1775_;
goto _start;
}
}
else
{
uint8_t v___x_1783_; 
v___x_1783_ = 0;
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object* v_k_1784_, lean_object* v_t_1785_){
_start:
{
uint64_t v_k_boxed_1786_; uint8_t v_res_1787_; lean_object* v_r_1788_; 
v_k_boxed_1786_ = lean_unbox_uint64(v_k_1784_);
lean_dec_ref(v_k_1784_);
v_res_1787_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_boxed_1786_, v_t_1785_);
lean_dec(v_t_1785_);
v_r_1788_ = lean_box(v_res_1787_);
return v_r_1788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object* v___x_1789_, uint64_t v_hash_1790_, lean_object* v_s_1791_){
_start:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1791_);
v___x_1793_ = lean_nat_dec_le(v___x_1789_, v___x_1792_);
lean_dec(v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v_toEnvExtension_1795_; lean_object* v_asyncMode_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1794_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1795_ = lean_ctor_get(v___x_1794_, 0);
v_asyncMode_1796_ = lean_ctor_get(v_toEnvExtension_1795_, 2);
v___x_1797_ = lean_box(1);
v___x_1798_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_1791_);
v___x_1799_ = lean_box(0);
v___x_1800_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1797_, v___x_1794_, v___x_1798_, v_asyncMode_1796_, v___x_1799_);
v___x_1801_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_hash_1790_, v___x_1800_);
lean_dec(v___x_1800_);
return v___x_1801_;
}
else
{
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object* v___x_1802_, lean_object* v_hash_1803_, lean_object* v_s_1804_){
_start:
{
uint64_t v_hash_boxed_1805_; uint8_t v_res_1806_; lean_object* v_r_1807_; 
v_hash_boxed_1805_ = lean_unbox_uint64(v_hash_1803_);
lean_dec_ref(v_hash_1803_);
v_res_1806_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1802_, v_hash_boxed_1805_, v_s_1804_);
lean_dec_ref(v_s_1804_);
lean_dec(v___x_1802_);
v_r_1807_ = lean_box(v_res_1806_);
return v_r_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object* v___x_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1808_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object* v___x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1812_, v___y_1813_);
lean_dec_ref(v___y_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object* v_snd_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_snd_1816_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_javascript_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v_javascript_1830_ = lean_ctor_get(v_a_1826_, 0);
lean_inc_ref(v_javascript_1830_);
lean_dec(v_a_1826_);
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_javascript_1830_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1825_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1825_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object* v_snd_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t v_hash_1854_, lean_object* v___x_1855_, lean_object* v_snap_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; lean_object* v_toEnvExtension_1860_; lean_object* v_asyncMode_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1859_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1860_ = lean_ctor_get(v___x_1859_, 0);
v_asyncMode_1861_ = lean_ctor_get(v_toEnvExtension_1860_, 2);
v___x_1862_ = lean_box(1);
v___x_1863_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1856_);
v___x_1864_ = lean_box(0);
v___x_1865_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1862_, v___x_1859_, v___x_1863_, v_asyncMode_1861_, v___x_1864_);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1865_, v_hash_1854_);
lean_dec(v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 1)
{
lean_object* v_val_1867_; lean_object* v_snd_1868_; lean_object* v___f_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v___x_1855_);
v_val_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v_snd_1868_ = lean_ctor_get(v_val_1867_, 1);
lean_inc(v_snd_1868_);
lean_dec(v_val_1867_);
v___f_1869_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__2___boxed), 9, 1);
lean_closure_set(v___f_1869_, 0, v_snd_1868_);
v___x_1870_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1856_, v___f_1869_, v___y_1857_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; 
lean_dec(v___x_1866_);
lean_dec_ref(v_snap_1856_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1855_);
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object* v_hash_1872_, lean_object* v___x_1873_, lean_object* v_snap_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint64_t v_hash_boxed_1877_; lean_object* v_res_1878_; 
v_hash_boxed_1877_ = lean_unbox_uint64(v_hash_1872_);
lean_dec_ref(v_hash_1872_);
v_res_1878_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_boxed_1877_, v___x_1873_, v_snap_1874_, v___y_1875_);
lean_dec_ref(v___y_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource(lean_object* v_args_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint64_t v_hash_1886_; lean_object* v_pos_1887_; lean_object* v___x_1888_; 
v___x_1884_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1885_ = lean_st_ref_get(v___x_1884_);
v_hash_1886_ = lean_ctor_get_uint64(v_args_1881_, sizeof(void*)*1);
v_pos_1887_ = lean_ctor_get(v_args_1881_, 0);
lean_inc_ref(v_pos_1887_);
lean_dec_ref(v_args_1881_);
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1885_, v_hash_1886_);
lean_dec(v___x_1885_);
if (lean_obj_tag(v___x_1888_) == 1)
{
lean_object* v_val_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_pos_1887_);
v_val_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_val_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_snd_1893_; lean_object* v_javascript_1894_; lean_object* v___x_1896_; 
v_snd_1893_ = lean_ctor_get(v_val_1889_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_val_1889_);
v_javascript_1894_ = lean_ctor_get(v_snd_1893_, 0);
lean_inc_ref(v_javascript_1894_);
lean_dec(v_snd_1893_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_javascript_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_javascript_1894_);
v___x_1896_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_task_pure(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
}
else
{
lean_object* v___x_1901_; lean_object* v_a_1902_; lean_object* v_toEditableDocumentCore_1903_; lean_object* v_meta_1904_; lean_object* v_text_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; 
lean_dec(v___x_1888_);
v___x_1901_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_1882_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1901_);
v_toEditableDocumentCore_1903_ = lean_ctor_get(v_a_1902_, 0);
v_meta_1904_ = lean_ctor_get(v_toEditableDocumentCore_1903_, 0);
v_text_1905_ = lean_ctor_get(v_meta_1904_, 3);
v___x_1906_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1905_, v_pos_1887_);
v___x_1907_ = lean_box_uint64(v_hash_1886_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1908_, 0, v___x_1906_);
lean_closure_set(v___f_1908_, 1, v___x_1907_);
v___x_1909_ = 3;
v___x_1910_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_1911_ = lean_uint64_to_nat(v_hash_1886_);
v___x_1912_ = l_Nat_reprFast(v___x_1911_);
v___x_1913_ = lean_string_append(v___x_1910_, v___x_1912_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_1915_ = lean_string_append(v___x_1913_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*1, v___x_1909_);
lean_inc_ref(v___x_1916_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1917_, 0, v___x_1916_);
v___x_1918_ = lean_box_uint64(v_hash_1886_);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1919_, 0, v___x_1918_);
lean_closure_set(v___f_1919_, 1, v___x_1916_);
v___x_1920_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1902_, v___f_1908_, v___f_1917_, v___f_1919_, v_a_1882_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object* v_args_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Widget_getWidgetSource(v_args_1921_, v_a_1922_);
lean_dec_ref(v_a_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object* v_00_u03b2_1925_, uint64_t v_k_1926_, lean_object* v_t_1927_){
_start:
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1926_, v_t_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object* v_00_u03b2_1929_, lean_object* v_k_1930_, lean_object* v_t_1931_){
_start:
{
uint64_t v_k_boxed_1932_; uint8_t v_res_1933_; lean_object* v_r_1934_; 
v_k_boxed_1932_ = lean_unbox_uint64(v_k_1930_);
lean_dec_ref(v_k_1930_);
v_res_1933_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(v_00_u03b2_1929_, v_k_boxed_1932_, v_t_1931_);
lean_dec(v_t_1931_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_1935_, lean_object* v_i_1936_, lean_object* v_k_1937_){
_start:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_get_size(v_keys_1935_);
v___x_1939_ = lean_nat_dec_lt(v_i_1936_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec(v_i_1936_);
return v___x_1939_;
}
else
{
lean_object* v_k_x27_1940_; uint8_t v___x_1941_; 
v_k_x27_1940_ = lean_array_fget_borrowed(v_keys_1935_, v_i_1936_);
v___x_1941_ = lean_name_eq(v_k_1937_, v_k_x27_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = lean_nat_add(v_i_1936_, v___x_1942_);
lean_dec(v_i_1936_);
v_i_1936_ = v___x_1943_;
goto _start;
}
else
{
lean_dec(v_i_1936_);
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_1945_, lean_object* v_i_1946_, lean_object* v_k_1947_){
_start:
{
uint8_t v_res_1948_; lean_object* v_r_1949_; 
v_res_1948_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1945_, v_i_1946_, v_k_1947_);
lean_dec(v_k_1947_);
lean_dec_ref(v_keys_1945_);
v_r_1949_ = lean_box(v_res_1948_);
return v_r_1949_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_1950_, size_t v_x_1951_, lean_object* v_x_1952_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 0)
{
lean_object* v_es_1953_; lean_object* v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v_j_1957_; lean_object* v___x_1958_; 
v_es_1953_ = lean_ctor_get(v_x_1950_, 0);
v___x_1954_ = lean_box(2);
v___x_1955_ = ((size_t)31ULL);
v___x_1956_ = lean_usize_land(v_x_1951_, v___x_1955_);
v_j_1957_ = lean_usize_to_nat(v___x_1956_);
v___x_1958_ = lean_array_get_borrowed(v___x_1954_, v_es_1953_, v_j_1957_);
lean_dec(v_j_1957_);
switch(lean_obj_tag(v___x_1958_))
{
case 0:
{
lean_object* v_key_1959_; uint8_t v___x_1960_; 
v_key_1959_ = lean_ctor_get(v___x_1958_, 0);
v___x_1960_ = lean_name_eq(v_x_1952_, v_key_1959_);
return v___x_1960_;
}
case 1:
{
lean_object* v_node_1961_; size_t v___x_1962_; size_t v___x_1963_; 
v_node_1961_ = lean_ctor_get(v___x_1958_, 0);
v___x_1962_ = ((size_t)5ULL);
v___x_1963_ = lean_usize_shift_right(v_x_1951_, v___x_1962_);
v_x_1950_ = v_node_1961_;
v_x_1951_ = v___x_1963_;
goto _start;
}
default: 
{
uint8_t v___x_1965_; 
v___x_1965_ = 0;
return v___x_1965_;
}
}
}
else
{
lean_object* v_ks_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_ks_1966_ = lean_ctor_get(v_x_1950_, 0);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_1966_, v___x_1967_, v_x_1952_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
size_t v_x_1062__boxed_1972_; uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_x_1062__boxed_1972_ = lean_unbox_usize(v_x_1970_);
lean_dec(v_x_1970_);
v_res_1973_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1969_, v_x_1062__boxed_1972_, v_x_1971_);
lean_dec(v_x_1971_);
lean_dec_ref(v_x_1969_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
uint64_t v___y_1978_; 
if (lean_obj_tag(v_x_1976_) == 0)
{
uint64_t v___x_1981_; 
v___x_1981_ = 1723ULL;
v___y_1978_ = v___x_1981_;
goto v___jp_1977_;
}
else
{
uint64_t v_hash_1982_; 
v_hash_1982_ = lean_ctor_get_uint64(v_x_1976_, sizeof(void*)*2);
v___y_1978_ = v_hash_1982_;
goto v___jp_1977_;
}
v___jp_1977_:
{
size_t v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = lean_uint64_to_usize(v___y_1978_);
v___x_1980_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1975_, v___x_1979_, v_x_1976_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_res_1985_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1983_, v_x_1984_);
lean_dec(v_x_1984_);
lean_dec_ref(v_x_1983_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v_ks_1991_; lean_object* v_vs_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2016_; 
v_ks_1991_ = lean_ctor_get(v_x_1987_, 0);
v_vs_1992_ = lean_ctor_get(v_x_1987_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1994_ = v_x_1987_;
v_isShared_1995_ = v_isSharedCheck_2016_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_vs_1992_);
lean_inc(v_ks_1991_);
lean_dec(v_x_1987_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2016_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = lean_array_get_size(v_ks_1991_);
v___x_1997_ = lean_nat_dec_lt(v_x_1988_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec(v_x_1988_);
v___x_1998_ = lean_array_push(v_ks_1991_, v_x_1989_);
v___x_1999_ = lean_array_push(v_vs_1992_, v_x_1990_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v___x_1999_);
lean_ctor_set(v___x_1994_, 0, v___x_1998_);
v___x_2001_ = v___x_1994_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v_k_x27_2003_; uint8_t v___x_2004_; 
v_k_x27_2003_ = lean_array_fget_borrowed(v_ks_1991_, v_x_1988_);
v___x_2004_ = lean_name_eq(v_x_1989_, v_k_x27_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2006_; 
if (v_isShared_1995_ == 0)
{
v___x_2006_ = v___x_1994_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_ks_1991_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_vs_1992_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_add(v_x_1988_, v___x_2007_);
lean_dec(v_x_1988_);
v_x_1987_ = v___x_2006_;
v_x_1988_ = v___x_2008_;
goto _start;
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2011_ = lean_array_fset(v_ks_1991_, v_x_1988_, v_x_1989_);
v___x_2012_ = lean_array_fset(v_vs_1992_, v_x_1988_, v_x_1990_);
lean_dec(v_x_1988_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v___x_2012_);
lean_ctor_set(v___x_1994_, 0, v___x_2011_);
v___x_2014_ = v___x_1994_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_n_2017_, lean_object* v_k_2018_, lean_object* v_v_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_n_2017_, v___x_2020_, v_k_2018_, v_v_2019_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_x_2023_, size_t v_x_2024_, size_t v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v_es_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v_j_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_es_2028_ = lean_ctor_get(v_x_2023_, 0);
v___x_2029_ = ((size_t)31ULL);
v___x_2030_ = lean_usize_land(v_x_2024_, v___x_2029_);
v_j_2031_ = lean_usize_to_nat(v___x_2030_);
v___x_2032_ = lean_array_get_size(v_es_2028_);
v___x_2033_ = lean_nat_dec_lt(v_j_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec(v_j_2031_);
lean_dec(v_x_2027_);
lean_dec(v_x_2026_);
return v_x_2023_;
}
else
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2072_; 
lean_inc_ref(v_es_2028_);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v_x_2023_, 0);
lean_dec(v_unused_2073_);
v___x_2035_ = v_x_2023_;
v_isShared_2036_ = v_isSharedCheck_2072_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v_x_2023_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2072_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_v_2037_; lean_object* v___x_2038_; lean_object* v_xs_x27_2039_; lean_object* v___y_2041_; 
v_v_2037_ = lean_array_fget(v_es_2028_, v_j_2031_);
v___x_2038_ = lean_box(0);
v_xs_x27_2039_ = lean_array_fset(v_es_2028_, v_j_2031_, v___x_2038_);
switch(lean_obj_tag(v_v_2037_))
{
case 0:
{
lean_object* v_key_2046_; lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_key_2046_ = lean_ctor_get(v_v_2037_, 0);
v_val_2047_ = lean_ctor_get(v_v_2037_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_v_2037_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v_v_2037_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_inc(v_key_2046_);
lean_dec(v_v_2037_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_name_eq(v_x_2026_, v_key_2046_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_del_object(v___x_2049_);
v___x_2052_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2046_, v_val_2047_, v_x_2026_, v_x_2027_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___y_2041_ = v___x_2053_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_val_2047_);
lean_dec(v_key_2046_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v_x_2027_);
lean_ctor_set(v___x_2049_, 0, v_x_2026_);
v___x_2055_ = v___x_2049_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_x_2026_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_x_2027_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v___y_2041_ = v___x_2055_;
goto v___jp_2040_;
}
}
}
}
case 1:
{
lean_object* v_node_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2070_; 
v_node_2058_ = lean_ctor_get(v_v_2037_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_v_2037_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2060_ = v_v_2037_;
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_node_2058_);
lean_dec(v_v_2037_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
size_t v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2062_ = ((size_t)5ULL);
v___x_2063_ = lean_usize_shift_right(v_x_2024_, v___x_2062_);
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_add(v_x_2025_, v___x_2064_);
v___x_2066_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_node_2058_, v___x_2063_, v___x_2065_, v_x_2026_, v_x_2027_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2066_);
v___x_2068_ = v___x_2060_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
v___y_2041_ = v___x_2068_;
goto v___jp_2040_;
}
}
}
default: 
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_x_2026_);
lean_ctor_set(v___x_2071_, 1, v_x_2027_);
v___y_2041_ = v___x_2071_;
goto v___jp_2040_;
}
}
v___jp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_array_fset(v_xs_x27_2039_, v_j_2031_, v___y_2041_);
lean_dec(v_j_2031_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2042_);
v___x_2044_ = v___x_2035_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_object* v_ks_2074_; lean_object* v_vs_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2093_; 
v_ks_2074_ = lean_ctor_get(v_x_2023_, 0);
v_vs_2075_ = lean_ctor_get(v_x_2023_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2077_ = v_x_2023_;
v_isShared_2078_ = v_isSharedCheck_2093_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_vs_2075_);
lean_inc(v_ks_2074_);
lean_dec(v_x_2023_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2093_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_ks_2074_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_vs_2075_);
v___x_2080_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v_newNode_2081_; size_t v___x_2082_; uint8_t v___x_2083_; 
v_newNode_2081_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v___x_2080_, v_x_2026_, v_x_2027_);
v___x_2082_ = ((size_t)7ULL);
v___x_2083_ = lean_usize_dec_le(v___x_2082_, v_x_2025_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2084_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2081_);
v___x_2085_ = lean_unsigned_to_nat(4u);
v___x_2086_ = lean_nat_dec_lt(v___x_2084_, v___x_2085_);
lean_dec(v___x_2084_);
if (v___x_2086_ == 0)
{
lean_object* v_ks_2087_; lean_object* v_vs_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_ks_2087_ = lean_ctor_get(v_newNode_2081_, 0);
lean_inc_ref(v_ks_2087_);
v_vs_2088_ = lean_ctor_get(v_newNode_2081_, 1);
lean_inc_ref(v_vs_2088_);
lean_dec_ref(v_newNode_2081_);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0);
v___x_2091_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_x_2025_, v_ks_2087_, v_vs_2088_, v___x_2089_, v___x_2090_);
lean_dec_ref(v_vs_2088_);
lean_dec_ref(v_ks_2087_);
return v___x_2091_;
}
else
{
return v_newNode_2081_;
}
}
else
{
return v_newNode_2081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t v_depth_2094_, lean_object* v_keys_2095_, lean_object* v_vals_2096_, lean_object* v_i_2097_, lean_object* v_entries_2098_){
_start:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_array_get_size(v_keys_2095_);
v___x_2100_ = lean_nat_dec_lt(v_i_2097_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec(v_i_2097_);
return v_entries_2098_;
}
else
{
lean_object* v_k_2101_; lean_object* v_v_2102_; uint64_t v___y_2104_; 
v_k_2101_ = lean_array_fget_borrowed(v_keys_2095_, v_i_2097_);
v_v_2102_ = lean_array_fget_borrowed(v_vals_2096_, v_i_2097_);
if (lean_obj_tag(v_k_2101_) == 0)
{
uint64_t v___x_2115_; 
v___x_2115_ = 1723ULL;
v___y_2104_ = v___x_2115_;
goto v___jp_2103_;
}
else
{
uint64_t v_hash_2116_; 
v_hash_2116_ = lean_ctor_get_uint64(v_k_2101_, sizeof(void*)*2);
v___y_2104_ = v_hash_2116_;
goto v___jp_2103_;
}
v___jp_2103_:
{
size_t v_h_2105_; size_t v___x_2106_; lean_object* v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v_h_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_h_2105_ = lean_uint64_to_usize(v___y_2104_);
v___x_2106_ = ((size_t)5ULL);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_sub(v_depth_2094_, v___x_2108_);
v___x_2110_ = lean_usize_mul(v___x_2106_, v___x_2109_);
v_h_2111_ = lean_usize_shift_right(v_h_2105_, v___x_2110_);
v___x_2112_ = lean_nat_add(v_i_2097_, v___x_2107_);
lean_dec(v_i_2097_);
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
v___x_2113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_entries_2098_, v_h_2111_, v_depth_2094_, v_k_2101_, v_v_2102_);
v_i_2097_ = v___x_2112_;
v_entries_2098_ = v___x_2113_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_depth_2117_, lean_object* v_keys_2118_, lean_object* v_vals_2119_, lean_object* v_i_2120_, lean_object* v_entries_2121_){
_start:
{
size_t v_depth_boxed_2122_; lean_object* v_res_2123_; 
v_depth_boxed_2122_ = lean_unbox_usize(v_depth_2117_);
lean_dec(v_depth_2117_);
v_res_2123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_boxed_2122_, v_keys_2118_, v_vals_2119_, v_i_2120_, v_entries_2121_);
lean_dec_ref(v_vals_2119_);
lean_dec_ref(v_keys_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
size_t v_x_1197__boxed_2129_; size_t v_x_1198__boxed_2130_; lean_object* v_res_2131_; 
v_x_1197__boxed_2129_ = lean_unbox_usize(v_x_2125_);
lean_dec(v_x_2125_);
v_x_1198__boxed_2130_ = lean_unbox_usize(v_x_2126_);
lean_dec(v_x_2126_);
v_res_2131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2124_, v_x_1197__boxed_2129_, v_x_1198__boxed_2130_, v_x_2127_, v_x_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
uint64_t v___y_2136_; 
if (lean_obj_tag(v_x_2133_) == 0)
{
uint64_t v___x_2140_; 
v___x_2140_ = 1723ULL;
v___y_2136_ = v___x_2140_;
goto v___jp_2135_;
}
else
{
uint64_t v_hash_2141_; 
v_hash_2141_ = lean_ctor_get_uint64(v_x_2133_, sizeof(void*)*2);
v___y_2136_ = v_hash_2141_;
goto v___jp_2135_;
}
v___jp_2135_:
{
size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_uint64_to_usize(v___y_2136_);
v___x_2138_ = ((size_t)1ULL);
v___x_2139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2132_, v___x_2137_, v___x_2138_, v_x_2133_, v_x_2134_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v___y_2142_){
_start:
{
lean_inc(v___y_2142_);
return v___y_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(v___y_2143_);
lean_dec(v___y_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object* v_expireTime_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_x_2146_);
lean_ctor_set(v___x_2147_, 1, v_expireTime_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object* v_val_2148_, lean_object* v___f_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_){
_start:
{
if (lean_obj_tag(v_x_2150_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v___f_2149_);
v_a_2153_ = lean_ctor_get(v_x_2150_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2150_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v_x_2150_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v_x_2150_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2184_; 
v_a_2161_ = lean_ctor_get(v_x_2150_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_x_2150_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2163_ = v_x_2150_;
v_isShared_2164_ = v_isSharedCheck_2184_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v_x_2150_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2184_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v_objects_2166_; lean_object* v_expireTime_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2183_; 
v___x_2165_ = lean_st_ref_take(v_val_2148_);
v_objects_2166_ = lean_ctor_get(v___x_2165_, 0);
v_expireTime_2167_ = lean_ctor_get(v___x_2165_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2169_ = v___x_2165_;
v_isShared_2170_ = v_isSharedCheck_2183_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_expireTime_2167_);
lean_inc(v_objects_2166_);
lean_dec(v___x_2165_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2183_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_2171_, 0, v_expireTime_2167_);
v___x_2172_ = l_Lean_Widget_instToJsonWidgetSource_toJson(v_a_2161_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v_objects_2166_);
lean_ctor_set(v___x_2169_, 0, v___x_2172_);
v___x_2174_ = v___x_2169_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_objects_2166_);
v___x_2174_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2175_ = l_Prod_map___redArg(v___f_2149_, v___f_2171_, v___x_2174_);
v_fst_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_fst_2176_);
v_snd_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_snd_2177_);
lean_dec_ref(v___x_2175_);
v___x_2178_ = lean_st_ref_put(v_val_2148_, v_snd_2177_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 0);
lean_ctor_set(v___x_2163_, 0, v_fst_2176_);
v___x_2180_ = v___x_2163_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_fst_2176_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object* v_val_2185_, lean_object* v___f_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2185_, v___f_2186_, v_x_2187_, v___y_2188_);
lean_dec_ref(v___y_2188_);
lean_dec(v_val_2185_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object* v___f_2198_, lean_object* v_method_2199_, lean_object* v_handler_2200_, uint64_t v_seshId_2201_, lean_object* v_j_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_rpcSessions_2205_; lean_object* v___x_2206_; 
v_rpcSessions_2205_ = lean_ctor_get(v___y_2203_, 0);
v___x_2206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_2205_, v_seshId_2201_);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc_n(v_val_2207_, 2);
lean_dec_ref_known(v___x_2206_, 1);
v___f_2208_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2208_, 0, v_val_2207_);
lean_closure_set(v___f_2208_, 1, v___f_2198_);
v___x_2209_ = lean_st_ref_get(v_val_2207_);
lean_dec(v_val_2207_);
lean_dec(v___x_2209_);
lean_inc(v_j_2202_);
v___x_2210_ = l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(v_j_2202_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref(v___f_2208_);
lean_dec_ref(v_handler_2200_);
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2231_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2231_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
uint8_t v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2215_ = 3;
v___x_2216_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_2217_ = 1;
v___x_2218_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2199_, v___x_2217_);
v___x_2219_ = lean_string_append(v___x_2216_, v___x_2218_);
lean_dec_ref(v___x_2218_);
v___x_2220_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_2221_ = lean_string_append(v___x_2219_, v___x_2220_);
v___x_2222_ = l_Lean_Json_compress(v_j_2202_);
v___x_2223_ = lean_string_append(v___x_2221_, v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_string_append(v___x_2225_, v_a_2211_);
lean_dec(v_a_2211_);
v___x_2227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___x_2215_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 1);
lean_ctor_set(v___x_2213_, 0, v___x_2227_);
v___x_2229_ = v___x_2213_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2233_; 
lean_dec(v_j_2202_);
lean_dec(v_method_2199_);
v_a_2232_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2210_, 1);
lean_inc_ref(v___y_2203_);
v___x_2233_ = lean_apply_3(v_handler_2200_, v_a_2232_, v___y_2203_, lean_box(0));
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_2234_, v___f_2208_, v___y_2203_);
return v___x_2235_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v___f_2208_);
v_a_2236_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2233_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2233_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v___x_2206_);
lean_dec(v_j_2202_);
lean_dec_ref(v_handler_2200_);
lean_dec(v_method_2199_);
lean_dec_ref(v___f_2198_);
v___x_2244_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object* v___f_2246_, lean_object* v_method_2247_, lean_object* v_handler_2248_, lean_object* v_seshId_2249_, lean_object* v_j_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint64_t v_seshId_boxed_2253_; lean_object* v_res_2254_; 
v_seshId_boxed_2253_ = lean_unbox_uint64(v_seshId_2249_);
lean_dec_ref(v_seshId_2249_);
v_res_2254_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v___f_2246_, v_method_2247_, v_handler_2248_, v_seshId_boxed_2253_, v_j_2250_, v___y_2251_);
lean_dec_ref(v___y_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_method_2256_, lean_object* v_handler_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___f_2259_; 
v___f_2258_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed), 7, 3);
lean_closure_set(v___f_2259_, 0, v___f_2258_);
lean_closure_set(v___f_2259_, 1, v_method_2256_);
lean_closure_set(v___f_2259_, 2, v_handler_2257_);
return v___f_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object* v_method_2264_, lean_object* v_handler_2265_){
_start:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v_errMsg_2272_; uint8_t v___x_2273_; 
v___x_2267_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_2268_ = 1;
lean_inc(v_method_2264_);
v___x_2269_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2264_, v___x_2268_);
v___x_2270_ = lean_string_append(v___x_2267_, v___x_2269_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_2272_ = lean_string_append(v___x_2270_, v___x_2271_);
v___x_2273_ = l_Lean_initializing();
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v_handler_2265_);
lean_dec(v_method_2264_);
v___x_2274_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_2275_ = lean_string_append(v_errMsg_2272_, v___x_2274_);
v___x_2276_ = lean_mk_io_user_error(v___x_2275_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_2279_ = lean_st_ref_get(v___x_2278_);
v___x_2280_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2279_, v_method_2264_);
lean_dec(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v_errMsg_2272_);
lean_inc(v_method_2264_);
v___x_2281_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(v_method_2264_, v_handler_2265_);
v___x_2282_ = lean_st_ref_take(v___x_2278_);
v___x_2283_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2282_, v_method_2264_, v___x_2281_);
v___x_2284_ = lean_st_ref_put(v___x_2278_, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_handler_2265_);
lean_dec(v_method_2264_);
v___x_2286_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_2287_ = lean_string_append(v_errMsg_2272_, v___x_2286_);
v___x_2288_ = lean_mk_io_user_error(v___x_2287_);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2290_, lean_object* v_handler_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2290_, v_handler_2291_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2302_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2303_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v___x_2301_, v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
return v_res_2305_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
uint8_t v___x_2309_; 
v___x_2309_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2307_, v_x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
uint8_t v_res_2313_; lean_object* v_r_2314_; 
v_res_2313_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2310_, v_x_2311_, v_x_2312_);
lean_dec(v_x_2312_);
lean_dec_ref(v_x_2311_);
v_r_2314_ = lean_box(v_res_2313_);
return v_r_2314_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_2315_){
_start:
{
lean_inc_ref(v_x_2315_);
return v_x_2315_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2316_);
lean_dec_ref(v_x_2316_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_, lean_object* v___y_2320_){
_start:
{
lean_inc_ref(v_x_2319_);
return v_x_2319_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b1_2321_, v_x_2322_, v___y_2323_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v_x_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2326_, v_x_2327_, v_x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2330_, lean_object* v_x_2331_, size_t v_x_2332_, lean_object* v_x_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2331_, v_x_2332_, v_x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
size_t v_x_1681__boxed_2339_; uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_x_1681__boxed_2339_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2340_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2335_, v_x_2336_, v_x_1681__boxed_2339_, v_x_2338_);
lean_dec(v_x_2338_);
lean_dec_ref(v_x_2336_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, size_t v_x_2344_, size_t v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2343_, v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
size_t v_x_1692__boxed_2355_; size_t v_x_1693__boxed_2356_; lean_object* v_res_2357_; 
v_x_1692__boxed_2355_ = lean_unbox_usize(v_x_2351_);
lean_dec(v_x_2351_);
v_x_1693__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_2349_, v_x_2350_, v_x_1692__boxed_2355_, v_x_1693__boxed_2356_, v_x_2353_, v_x_2354_);
return v_res_2357_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2358_, lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_heq_2361_, lean_object* v_i_2362_, lean_object* v_k_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2359_, v_i_2362_, v_k_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_k_2370_){
_start:
{
uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_res_2371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2365_, v_keys_2366_, v_vals_2367_, v_heq_2368_, v_i_2369_, v_k_2370_);
lean_dec(v_k_2370_);
lean_dec_ref(v_vals_2367_);
lean_dec_ref(v_keys_2366_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_2373_, lean_object* v_n_2374_, lean_object* v_k_2375_, lean_object* v_v_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v_n_2374_, v_k_2375_, v_v_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2378_, size_t v_depth_2379_, lean_object* v_keys_2380_, lean_object* v_vals_2381_, lean_object* v_heq_2382_, lean_object* v_i_2383_, lean_object* v_entries_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2379_, v_keys_2380_, v_vals_2381_, v_i_2383_, v_entries_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2386_, lean_object* v_depth_2387_, lean_object* v_keys_2388_, lean_object* v_vals_2389_, lean_object* v_heq_2390_, lean_object* v_i_2391_, lean_object* v_entries_2392_){
_start:
{
size_t v_depth_boxed_2393_; lean_object* v_res_2394_; 
v_depth_boxed_2393_ = lean_unbox_usize(v_depth_2387_);
lean_dec(v_depth_2387_);
v_res_2394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(v_00_u03b2_2386_, v_depth_boxed_2393_, v_keys_2388_, v_vals_2389_, v_heq_2390_, v_i_2391_, v_entries_2392_);
lean_dec_ref(v_vals_2389_);
lean_dec_ref(v_keys_2388_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_x_2396_, v_x_2397_, v_x_2398_, v_x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(lean_object* v_x_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_obj_tag_nat(v_x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl___boxed(lean_object* v_x_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(v_x_2403_);
lean_dec_ref(v_x_2403_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object* v_t_2405_, lean_object* v_k_2406_){
_start:
{
if (lean_obj_tag(v_t_2405_) == 0)
{
lean_object* v_n_2407_; lean_object* v___x_2408_; 
v_n_2407_ = lean_ctor_get(v_t_2405_, 0);
lean_inc(v_n_2407_);
lean_dec_ref_known(v_t_2405_, 1);
v___x_2408_ = lean_apply_1(v_k_2406_, v_n_2407_);
return v___x_2408_;
}
else
{
lean_object* v_wi_2409_; lean_object* v___x_2410_; 
v_wi_2409_ = lean_ctor_get(v_t_2405_, 0);
lean_inc_ref(v_wi_2409_);
lean_dec_ref_known(v_t_2405_, 1);
v___x_2410_ = lean_apply_1(v_k_2406_, v_wi_2409_);
return v___x_2410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object* v_motive_2411_, lean_object* v_ctorIdx_2412_, lean_object* v_t_2413_, lean_object* v_h_2414_, lean_object* v_k_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2413_, v_k_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object* v_motive_2417_, lean_object* v_ctorIdx_2418_, lean_object* v_t_2419_, lean_object* v_h_2420_, lean_object* v_k_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(v_motive_2417_, v_ctorIdx_2418_, v_t_2419_, v_h_2420_, v_k_2421_);
lean_dec(v_ctorIdx_2418_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object* v_t_2423_, lean_object* v_global_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2423_, v_global_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object* v_motive_2426_, lean_object* v_t_2427_, lean_object* v_h_2428_, lean_object* v_global_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2427_, v_global_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object* v_t_2431_, lean_object* v_local_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2431_, v_local_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object* v_motive_2434_, lean_object* v_t_2435_, lean_object* v_h_2436_, lean_object* v_local_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2435_, v_local_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2439_, uint64_t v_k_2440_, lean_object* v_fallback_2441_){
_start:
{
if (lean_obj_tag(v_t_2439_) == 0)
{
lean_object* v_k_2442_; lean_object* v_v_2443_; lean_object* v_l_2444_; lean_object* v_r_2445_; uint64_t v___x_2446_; uint8_t v___x_2447_; 
v_k_2442_ = lean_ctor_get(v_t_2439_, 1);
v_v_2443_ = lean_ctor_get(v_t_2439_, 2);
v_l_2444_ = lean_ctor_get(v_t_2439_, 3);
v_r_2445_ = lean_ctor_get(v_t_2439_, 4);
v___x_2446_ = lean_unbox_uint64(v_k_2442_);
v___x_2447_ = lean_uint64_dec_lt(v_k_2440_, v___x_2446_);
if (v___x_2447_ == 0)
{
uint64_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = lean_unbox_uint64(v_k_2442_);
v___x_2449_ = lean_uint64_dec_eq(v_k_2440_, v___x_2448_);
if (v___x_2449_ == 0)
{
v_t_2439_ = v_r_2445_;
goto _start;
}
else
{
lean_inc(v_v_2443_);
return v_v_2443_;
}
}
else
{
v_t_2439_ = v_l_2444_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2441_);
return v_fallback_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2452_, lean_object* v_k_2453_, lean_object* v_fallback_2454_){
_start:
{
uint64_t v_k_boxed_2455_; lean_object* v_res_2456_; 
v_k_boxed_2455_ = lean_unbox_uint64(v_k_2453_);
lean_dec_ref(v_k_2453_);
v_res_2456_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2452_, v_k_boxed_2455_, v_fallback_2454_);
lean_dec(v_fallback_2454_);
lean_dec(v_t_2452_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_s_2457_, lean_object* v_x_2458_){
_start:
{
lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2473_; 
v_fst_2459_ = lean_ctor_get(v_x_2458_, 0);
v_snd_2460_ = lean_ctor_get(v_x_2458_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_x_2458_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2462_ = v_x_2458_;
v_isShared_2463_ = v_isSharedCheck_2473_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_inc(v_fst_2459_);
lean_dec(v_x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2473_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; uint64_t v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_snd_2460_);
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_unbox_uint64(v_fst_2459_);
v___x_2467_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_s_2457_, v___x_2466_, v___x_2465_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set_tag(v___x_2462_, 1);
lean_ctor_set(v___x_2462_, 1, v___x_2467_);
lean_ctor_set(v___x_2462_, 0, v___x_2464_);
v___x_2469_ = v___x_2462_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
uint64_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_unbox_uint64(v_fst_2459_);
lean_dec(v_fst_2459_);
v___x_2471_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_2470_, v___x_2469_, v_s_2457_);
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_x_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2476_, 0, v_a_2475_);
lean_inc_ref_n(v___x_2476_, 2);
v___x_2477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
lean_ctor_set(v___x_2477_, 2, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_x_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v_x_2478_, v_a_2479_);
lean_dec_ref(v_x_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v___y_2481_){
_start:
{
lean_inc(v___y_2481_);
return v___y_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v___y_2482_);
lean_dec(v___y_2482_);
return v_res_2483_;
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
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2516_);
return v___x_2522_;
}
else
{
lean_object* v_head_2523_; 
v_head_2523_ = lean_ctor_get(v_as_x27_2515_, 0);
if (lean_obj_tag(v_head_2523_) == 0)
{
lean_object* v_tail_2524_; lean_object* v_n_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_tail_2524_ = lean_ctor_get(v_as_x27_2515_, 1);
v_n_2525_ = lean_ctor_get(v_head_2523_, 0);
v___x_2526_ = lean_box(0);
lean_inc(v_n_2525_);
v___x_2527_ = l_Lean_mkConst(v_n_2525_, v___x_2526_);
v___x_2528_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v___x_2527_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_array_push(v_b_2516_, v_a_2529_);
v_as_x27_2515_ = v_tail_2524_;
v_b_2516_ = v___x_2530_;
goto _start;
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
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
v_wi_2541_ = lean_ctor_get(v_head_2523_, 0);
lean_inc_ref(v_wi_2541_);
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
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v_as_x27_2544_);
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
v_l_2560_ = lean_ctor_get(v_x_2553_, 3);
v_r_2561_ = lean_ctor_get(v_x_2553_, 4);
v___x_2562_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2552_, v_l_2560_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v_a_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_a_2564_);
lean_dec(v_a_2563_);
v___x_2565_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_v_2559_, v_a_2564_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v_init_2552_ = v_a_2566_;
v_x_2553_ = v_r_2561_;
goto _start;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
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
return v___x_2562_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
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
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v_x_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets(lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_ret_2593_; lean_object* v___x_2594_; lean_object* v_env_2595_; lean_object* v___x_2596_; lean_object* v_ext_2597_; lean_object* v_toEnvExtension_2598_; lean_object* v_asyncMode_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_ret_2593_ = ((lean_object*)(l_Lean_Widget_evalPanelWidgets___closed__0));
v___x_2594_ = lean_st_ref_get(v_a_2591_);
v_env_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc_ref(v_env_2595_);
lean_dec(v___x_2594_);
v___x_2596_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v_ext_2597_ = lean_ctor_get(v___x_2596_, 1);
v_toEnvExtension_2598_ = lean_ctor_get(v_ext_2597_, 0);
v_asyncMode_2599_ = lean_ctor_get(v_toEnvExtension_2598_, 2);
v___x_2600_ = lean_box(1);
v___x_2601_ = 0;
v___x_2602_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2600_, v___x_2596_, v_env_2595_, v_asyncMode_2599_, v___x_2601_);
v___x_2603_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_ret_2593_, v___x_2602_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v___x_2602_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_a_2608_; lean_object* v___x_2610_; 
v_a_2608_ = lean_ctor_get(v_a_2604_, 0);
lean_inc(v_a_2608_);
lean_dec(v_a_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_a_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v_a_2613_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2603_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2603_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Widget_evalPanelWidgets(v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object* v_as_2627_, lean_object* v_as_x27_2628_, lean_object* v_b_2629_, lean_object* v_a_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2628_, v_b_2629_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object* v_as_2637_, lean_object* v_as_x27_2638_, lean_object* v_b_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2637_, v_as_x27_2638_, v_b_2639_, v_a_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v_as_x27_2638_);
lean_dec(v_as_2637_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, uint64_t v_h_2650_, lean_object* v_n_2651_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2652_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2653_ = lean_box_uint64(v_h_2650_);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v_n_2651_);
v___x_2655_ = 0;
v___x_2656_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2647_, v_inst_2649_, v_inst_2648_, v___x_2652_, v___x_2654_, v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_h_2660_, lean_object* v_n_2661_){
_start:
{
uint64_t v_h_boxed_2662_; lean_object* v_res_2663_; 
v_h_boxed_2662_ = lean_unbox_uint64(v_h_2660_);
lean_dec_ref(v_h_2660_);
v_res_2663_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2657_, v_inst_2658_, v_inst_2659_, v_h_boxed_2662_, v_n_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object* v_m_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, uint64_t v_h_2668_, lean_object* v_n_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2665_, v_inst_2666_, v_inst_2667_, v_h_2668_, v_n_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object* v_m_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_h_2675_, lean_object* v_n_2676_){
_start:
{
uint64_t v_h_boxed_2677_; lean_object* v_res_2678_; 
v_h_boxed_2677_ = lean_unbox_uint64(v_h_2675_);
lean_dec_ref(v_h_2675_);
v_res_2678_ = l_Lean_Widget_addPanelWidgetGlobal(v_m_2671_, v_inst_2672_, v_inst_2673_, v_inst_2674_, v_h_boxed_2677_, v_n_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, uint64_t v_h_2682_, lean_object* v_n_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; 
v___x_2684_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2685_ = lean_box_uint64(v_h_2682_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v_n_2683_);
v___x_2687_ = 2;
v___x_2688_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2679_, v_inst_2681_, v_inst_2680_, v___x_2684_, v___x_2686_, v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_h_2692_, lean_object* v_n_2693_){
_start:
{
uint64_t v_h_boxed_2694_; lean_object* v_res_2695_; 
v_h_boxed_2694_ = lean_unbox_uint64(v_h_2692_);
lean_dec_ref(v_h_2692_);
v_res_2695_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_h_boxed_2694_, v_n_2693_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object* v_m_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, uint64_t v_h_2700_, lean_object* v_n_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2697_, v_inst_2698_, v_inst_2699_, v_h_2700_, v_n_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object* v_m_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_h_2707_, lean_object* v_n_2708_){
_start:
{
uint64_t v_h_boxed_2709_; lean_object* v_res_2710_; 
v_h_boxed_2709_ = lean_unbox_uint64(v_h_2707_);
lean_dec_ref(v_h_2707_);
v_res_2710_ = l_Lean_Widget_addPanelWidgetScoped(v_m_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_h_boxed_2709_, v_n_2708_);
return v_res_2710_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t v_x_2711_, uint64_t v_y_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_uint64_dec_lt(v_x_2711_, v_y_2712_);
if (v___x_2713_ == 0)
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_uint64_dec_eq(v_x_2711_, v_y_2712_);
if (v___x_2714_ == 0)
{
uint8_t v___x_2715_; 
v___x_2715_ = 2;
return v___x_2715_;
}
else
{
uint8_t v___x_2716_; 
v___x_2716_ = 1;
return v___x_2716_;
}
}
else
{
uint8_t v___x_2717_; 
v___x_2717_ = 0;
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object* v_x_2718_, lean_object* v_y_2719_){
_start:
{
uint64_t v_x_boxed_2720_; uint64_t v_y_boxed_2721_; uint8_t v_res_2722_; lean_object* v_r_2723_; 
v_x_boxed_2720_ = lean_unbox_uint64(v_x_2718_);
lean_dec_ref(v_x_2718_);
v_y_boxed_2721_ = lean_unbox_uint64(v_y_2719_);
lean_dec_ref(v_y_2719_);
v_res_2722_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_boxed_2720_, v_y_boxed_2721_);
v_r_2723_ = lean_box(v_res_2722_);
return v_r_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object* v_wi_2724_, lean_object* v___f_2725_, lean_object* v_s_2726_){
_start:
{
uint64_t v_javascriptHash_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_javascriptHash_2727_ = lean_ctor_get_uint64(v_wi_2724_, sizeof(void*)*2);
v___x_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_wi_2724_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_box_uint64(v_javascriptHash_2727_);
lean_inc(v_s_2726_);
lean_inc_ref(v___f_2725_);
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___f_2725_, v_s_2726_, v___x_2730_, v___x_2729_);
v___x_2732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2728_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_box_uint64(v_javascriptHash_2727_);
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2725_, v___x_2733_, v___x_2732_, v_s_2726_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object* v___f_2735_, lean_object* v_env_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2738_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2737_, v_env_2736_, v___f_2735_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object* v_inst_2740_, lean_object* v_wi_2741_){
_start:
{
lean_object* v_modifyEnv_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; 
v_modifyEnv_2742_ = lean_ctor_get(v_inst_2740_, 1);
lean_inc(v_modifyEnv_2742_);
lean_dec_ref(v_inst_2740_);
v___f_2743_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___f_2744_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2744_, 0, v_wi_2741_);
lean_closure_set(v___f_2744_, 1, v___f_2743_);
v___f_2745_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2745_, 0, v___f_2744_);
v___x_2746_ = lean_apply_1(v_modifyEnv_2742_, v___f_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object* v_m_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_wi_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Widget_addPanelWidgetLocal___redArg(v_inst_2749_, v_wi_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object* v_m_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_wi_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Widget_addPanelWidgetLocal(v_m_2752_, v_inst_2753_, v_inst_2754_, v_wi_2755_);
lean_dec_ref(v_inst_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object* v___f_2757_, uint64_t v_h_2758_, lean_object* v_st_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_box_uint64(v_h_2758_);
v___x_2761_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___f_2757_, v___x_2760_, v_st_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object* v___f_2762_, lean_object* v_h_2763_, lean_object* v_st_2764_){
_start:
{
uint64_t v_h_boxed_2765_; lean_object* v_res_2766_; 
v_h_boxed_2765_ = lean_unbox_uint64(v_h_2763_);
lean_dec_ref(v_h_2763_);
v_res_2766_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2762_, v_h_boxed_2765_, v_st_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object* v_inst_2767_, uint64_t v_h_2768_){
_start:
{
lean_object* v_modifyEnv_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; 
v_modifyEnv_2769_ = lean_ctor_get(v_inst_2767_, 1);
lean_inc(v_modifyEnv_2769_);
lean_dec_ref(v_inst_2767_);
v___f_2770_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___x_2771_ = lean_box_uint64(v_h_2768_);
v___f_2772_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2772_, 0, v___f_2770_);
lean_closure_set(v___f_2772_, 1, v___x_2771_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2773_, 0, v___f_2772_);
v___x_2774_ = lean_apply_1(v_modifyEnv_2769_, v___f_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object* v_inst_2775_, lean_object* v_h_2776_){
_start:
{
uint64_t v_h_boxed_2777_; lean_object* v_res_2778_; 
v_h_boxed_2777_ = lean_unbox_uint64(v_h_2776_);
lean_dec_ref(v_h_2776_);
v_res_2778_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2775_, v_h_boxed_2777_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget(lean_object* v_m_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, uint64_t v_h_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2781_, v_h_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object* v_m_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_h_2787_){
_start:
{
uint64_t v_h_boxed_2788_; lean_object* v_res_2789_; 
v_h_boxed_2788_ = lean_unbox_uint64(v_h_2787_);
lean_dec_ref(v_h_2787_);
v_res_2789_ = l_Lean_Widget_erasePanelWidget(v_m_2784_, v_inst_2785_, v_inst_2786_, v_h_boxed_2788_);
lean_dec_ref(v_inst_2785_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t v_hash_2790_, lean_object* v_props_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___x_2795_; lean_object* v_env_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_val_2800_; lean_object* v___x_2803_; 
v___x_2795_ = lean_st_ref_get(v_a_2793_);
v_env_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc_ref(v_env_2796_);
lean_dec(v___x_2795_);
v___x_2797_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_2798_ = lean_st_ref_get(v___x_2797_);
v___x_2803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_2798_, v_hash_2790_);
lean_dec(v___x_2798_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2804_; lean_object* v_toEnvExtension_2805_; lean_object* v_asyncMode_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2804_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_2805_ = lean_ctor_get(v___x_2804_, 0);
v_asyncMode_2806_ = lean_ctor_get(v_toEnvExtension_2805_, 2);
v___x_2807_ = lean_box(1);
v___x_2808_ = lean_box(0);
v___x_2809_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2807_, v___x_2804_, v_env_2796_, v_asyncMode_2806_, v___x_2808_);
v___x_2810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_2809_, v_hash_2790_);
lean_dec(v___x_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref(v_props_2791_);
v___x_2811_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_2812_ = lean_uint64_to_nat(v_hash_2790_);
v___x_2813_ = l_Nat_reprFast(v___x_2812_);
v___x_2814_ = lean_string_append(v___x_2811_, v___x_2813_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_2816_ = lean_string_append(v___x_2814_, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
v___x_2818_ = l_Lean_MessageData_ofFormat(v___x_2817_);
v___x_2819_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v___x_2818_, v_a_2792_, v_a_2793_);
return v___x_2819_;
}
else
{
lean_object* v_val_2820_; lean_object* v_fst_2821_; 
v_val_2820_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_val_2820_);
lean_dec_ref_known(v___x_2810_, 1);
v_fst_2821_ = lean_ctor_get(v_val_2820_, 0);
lean_inc(v_fst_2821_);
lean_dec(v_val_2820_);
v_val_2800_ = v_fst_2821_;
goto v___jp_2799_;
}
}
else
{
lean_object* v_val_2822_; lean_object* v_fst_2823_; 
lean_dec_ref(v_env_2796_);
v_val_2822_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v___x_2803_, 1);
v_fst_2823_ = lean_ctor_get(v_val_2822_, 0);
lean_inc(v_fst_2823_);
lean_dec(v_val_2822_);
v_val_2800_ = v_fst_2823_;
goto v___jp_2799_;
}
v___jp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2801_, 0, v_val_2800_);
lean_ctor_set(v___x_2801_, 1, v_props_2791_);
lean_ctor_set_uint64(v___x_2801_, sizeof(void*)*2, v_hash_2790_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object* v_hash_2824_, lean_object* v_props_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
uint64_t v_hash_boxed_2829_; lean_object* v_res_2830_; 
v_hash_boxed_2829_ = lean_unbox_uint64(v_hash_2824_);
lean_dec_ref(v_hash_2824_);
v_res_2830_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_boxed_2829_, v_props_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object* v_t_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_infoState_2835_; uint8_t v_enabled_2836_; 
v___x_2834_ = lean_st_ref_get(v___y_2832_);
v_infoState_2835_ = lean_ctor_get(v___x_2834_, 8);
lean_inc_ref(v_infoState_2835_);
lean_dec(v___x_2834_);
v_enabled_2836_ = lean_ctor_get_uint8(v_infoState_2835_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2835_);
if (v_enabled_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec_ref(v_t_2831_);
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
else
{
lean_object* v___x_2839_; lean_object* v_infoState_2840_; lean_object* v_env_2841_; lean_object* v_nextMacroScope_2842_; lean_object* v_ngen_2843_; lean_object* v_auxDeclNGen_2844_; lean_object* v_traceState_2845_; lean_object* v_cache_2846_; lean_object* v_recordedDeps_2847_; lean_object* v_messages_2848_; lean_object* v_snapshotTasks_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2871_; 
v___x_2839_ = lean_st_ref_take(v___y_2832_);
v_infoState_2840_ = lean_ctor_get(v___x_2839_, 8);
v_env_2841_ = lean_ctor_get(v___x_2839_, 0);
v_nextMacroScope_2842_ = lean_ctor_get(v___x_2839_, 1);
v_ngen_2843_ = lean_ctor_get(v___x_2839_, 2);
v_auxDeclNGen_2844_ = lean_ctor_get(v___x_2839_, 3);
v_traceState_2845_ = lean_ctor_get(v___x_2839_, 4);
v_cache_2846_ = lean_ctor_get(v___x_2839_, 5);
v_recordedDeps_2847_ = lean_ctor_get(v___x_2839_, 6);
v_messages_2848_ = lean_ctor_get(v___x_2839_, 7);
v_snapshotTasks_2849_ = lean_ctor_get(v___x_2839_, 9);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2851_ = v___x_2839_;
v_isShared_2852_ = v_isSharedCheck_2871_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snapshotTasks_2849_);
lean_inc(v_infoState_2840_);
lean_inc(v_messages_2848_);
lean_inc(v_recordedDeps_2847_);
lean_inc(v_cache_2846_);
lean_inc(v_traceState_2845_);
lean_inc(v_auxDeclNGen_2844_);
lean_inc(v_ngen_2843_);
lean_inc(v_nextMacroScope_2842_);
lean_inc(v_env_2841_);
lean_dec(v___x_2839_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2871_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
uint8_t v_enabled_2853_; lean_object* v_assignment_2854_; lean_object* v_lazyAssignment_2855_; lean_object* v_trees_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2870_; 
v_enabled_2853_ = lean_ctor_get_uint8(v_infoState_2840_, sizeof(void*)*3);
v_assignment_2854_ = lean_ctor_get(v_infoState_2840_, 0);
v_lazyAssignment_2855_ = lean_ctor_get(v_infoState_2840_, 1);
v_trees_2856_ = lean_ctor_get(v_infoState_2840_, 2);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_infoState_2840_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2858_ = v_infoState_2840_;
v_isShared_2859_ = v_isSharedCheck_2870_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_trees_2856_);
lean_inc(v_lazyAssignment_2855_);
lean_inc(v_assignment_2854_);
lean_dec(v_infoState_2840_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2870_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = l_Lean_PersistentArray_push___redArg(v_trees_2856_, v_t_2831_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 2, v___x_2861_);
v___x_2863_ = v___x_2858_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_assignment_2854_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_lazyAssignment_2855_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v___x_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*3, v_enabled_2853_);
v___x_2863_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2865_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 8, v___x_2863_);
v___x_2865_ = v___x_2851_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_env_2841_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_nextMacroScope_2842_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_ngen_2843_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_auxDeclNGen_2844_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_traceState_2845_);
lean_ctor_set(v_reuseFailAlloc_2868_, 5, v_cache_2846_);
lean_ctor_set(v_reuseFailAlloc_2868_, 6, v_recordedDeps_2847_);
lean_ctor_set(v_reuseFailAlloc_2868_, 7, v_messages_2848_);
lean_ctor_set(v_reuseFailAlloc_2868_, 8, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2868_, 9, v_snapshotTasks_2849_);
v___x_2865_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_st_ref_put(v___y_2832_, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2860_);
return v___x_2867_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2872_, v___y_2873_);
lean_dec(v___y_2873_);
return v_res_2875_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = lean_unsigned_to_nat(32u);
v___x_2877_ = lean_mk_empty_array_with_capacity(v___x_2876_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2879_ = ((size_t)5ULL);
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = lean_unsigned_to_nat(32u);
v___x_2882_ = lean_mk_empty_array_with_capacity(v___x_2881_);
v___x_2883_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0);
v___x_2884_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v___x_2882_);
lean_ctor_set(v___x_2884_, 2, v___x_2880_);
lean_ctor_set(v___x_2884_, 3, v___x_2880_);
lean_ctor_set_usize(v___x_2884_, 4, v___x_2879_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object* v_t_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v_infoState_2890_; uint8_t v_enabled_2891_; 
v___x_2889_ = lean_st_ref_get(v___y_2887_);
v_infoState_2890_ = lean_ctor_get(v___x_2889_, 8);
lean_inc_ref(v_infoState_2890_);
lean_dec(v___x_2889_);
v_enabled_2891_ = lean_ctor_get_uint8(v_infoState_2890_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2890_);
if (v_enabled_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_dec_ref(v_t_2885_);
v___x_2892_ = lean_box(0);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1);
v___x_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2895_, 0, v_t_2885_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v___x_2895_, v___y_2887_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object* v_t_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t v_hash_2902_, lean_object* v_props_2903_, lean_object* v_stx_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2902_, v_props_2903_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2909_);
lean_ctor_set(v___x_2910_, 1, v_stx_2904_);
v___x_2911_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
v___x_2912_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v___x_2911_, v_a_2905_, v_a_2906_);
return v___x_2912_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_stx_2904_);
v_a_2913_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2908_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2908_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object* v_hash_2921_, lean_object* v_props_2922_, lean_object* v_stx_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
uint64_t v_hash_boxed_2927_; lean_object* v_res_2928_; 
v_hash_boxed_2927_ = lean_unbox_uint64(v_hash_2921_);
lean_dec_ref(v_hash_2921_);
v_res_2928_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_boxed_2927_, v_props_2922_, v_stx_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object* v_t_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2929_, v___y_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object* v_t_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object* v_x_2945_){
_start:
{
lean_object* v_name_2946_; lean_object* v_javascript_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2967_; 
v_name_2946_ = lean_ctor_get(v_x_2945_, 0);
v_javascript_2947_ = lean_ctor_get(v_x_2945_, 1);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_x_2945_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2949_ = v_x_2945_;
v_isShared_2950_ = v_isSharedCheck_2967_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_javascript_2947_);
lean_inc(v_name_2946_);
lean_dec(v_x_2945_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2967_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_2952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_name_2946_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_2952_);
lean_ctor_set(v___x_2949_, 0, v___x_2951_);
v___x_2954_ = v___x_2949_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_2958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_javascript_2947_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2955_);
v___x_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2955_);
v___x_2962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2956_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_2964_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_2962_, v___x_2963_);
v___x_2965_ = l_Lean_Json_mkObj(v___x_2964_);
lean_dec(v___x_2964_);
return v___x_2965_;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = 1;
v___x_2976_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_2977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2976_, v___x_2975_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_2979_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2);
v___x_2980_ = lean_string_append(v___x_2979_, v___x_2978_);
return v___x_2980_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = 1;
v___x_2984_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4));
v___x_2985_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2984_, v___x_2983_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5);
v___x_2987_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2988_ = lean_string_append(v___x_2987_, v___x_2986_);
return v___x_2988_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2990_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6);
v___x_2991_ = lean_string_append(v___x_2990_, v___x_2989_);
return v___x_2991_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = 1;
v___x_2995_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8));
v___x_2996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2995_, v___x_2994_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9);
v___x_2998_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2999_ = lean_string_append(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_3001_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10);
v___x_3002_ = lean_string_append(v___x_3001_, v___x_3000_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object* v_json_3003_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
lean_inc(v_json_3003_);
v___x_3005_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3003_, v___x_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v_json_3003_);
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3015_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3015_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3010_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7);
v___x_3011_ = lean_string_append(v___x_3010_, v_a_3006_);
lean_dec(v_a_3006_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3011_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_json_3003_);
v_a_3016_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3005_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3005_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set_tag(v___x_3018_, 0);
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_a_3024_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3025_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_3026_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3003_, v___x_3025_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_a_3024_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3036_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3036_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3031_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11);
v___x_3032_ = lean_string_append(v___x_3031_, v_a_3027_);
lean_dec(v_a_3027_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3032_);
v___x_3034_ = v___x_3029_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_a_3024_);
v_a_3037_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3026_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3026_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set_tag(v___x_3039_, 0);
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3053_; 
v_a_3045_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3047_ = v___x_3026_;
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3026_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v_a_3024_);
lean_ctor_set(v___x_3049_, 1, v_a_3045_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object* v_uwd_3056_){
_start:
{
lean_object* v_javascript_3057_; uint64_t v___x_3058_; lean_object* v___x_3059_; 
v_javascript_3057_ = lean_ctor_get(v_uwd_3056_, 1);
v___x_3058_ = lean_string_hash(v_javascript_3057_);
lean_inc_ref(v_javascript_3057_);
v___x_3059_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3059_, 0, v_javascript_3057_);
lean_ctor_set_uint64(v___x_3059_, sizeof(void*)*1, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object* v_uwd_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(v_uwd_3060_);
lean_dec_ref(v_uwd_3060_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object* v_____do__lift_3064_, lean_object* v_id_3065_, lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v___x_3068_, lean_object* v_____do__lift_3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3071_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_3064_, v_____do__lift_3069_, v___x_3070_, v_id_3065_);
v___x_3072_ = l_Lean_ofExcept___redArg(v_inst_3066_, v_inst_3067_, v___x_3068_, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object* v_____do__lift_3073_, lean_object* v_id_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v___x_3077_, lean_object* v_____do__lift_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(v_____do__lift_3073_, v_id_3074_, v_inst_3075_, v_inst_3076_, v___x_3077_, v_____do__lift_3078_);
lean_dec_ref(v_____do__lift_3078_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object* v_inst_3080_, lean_object* v_id_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v___x_3084_, lean_object* v_toBind_3085_, lean_object* v_____do__lift_3086_){
_start:
{
lean_object* v_getOptions_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; 
v_getOptions_3087_ = lean_ctor_get(v_inst_3080_, 0);
lean_inc(v_getOptions_3087_);
lean_dec_ref(v_inst_3080_);
v___f_3088_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_3088_, 0, v_____do__lift_3086_);
lean_closure_set(v___f_3088_, 1, v_id_3081_);
lean_closure_set(v___f_3088_, 2, v_inst_3082_);
lean_closure_set(v___f_3088_, 3, v_inst_3083_);
lean_closure_set(v___f_3088_, 4, v___x_3084_);
v___x_3089_ = lean_apply_4(v_toBind_3085_, lean_box(0), lean_box(0), v_getOptions_3087_, v___f_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_id_3095_){
_start:
{
lean_object* v_toBind_3096_; lean_object* v_getEnv_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; 
v_toBind_3096_ = lean_ctor_get(v_inst_3091_, 1);
lean_inc_n(v_toBind_3096_, 2);
v_getEnv_3097_ = lean_ctor_get(v_inst_3092_, 0);
lean_inc(v_getEnv_3097_);
lean_dec_ref(v_inst_3092_);
v___x_3098_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0));
v___f_3099_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3099_, 0, v_inst_3093_);
lean_closure_set(v___f_3099_, 1, v_id_3095_);
lean_closure_set(v___f_3099_, 2, v_inst_3091_);
lean_closure_set(v___f_3099_, 3, v_inst_3094_);
lean_closure_set(v___f_3099_, 4, v___x_3098_);
lean_closure_set(v___f_3099_, 5, v_toBind_3096_);
v___x_3100_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v_getEnv_3097_, v___f_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object* v_m_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_inst_3105_, lean_object* v_id_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(v_inst_3102_, v_inst_3103_, v_inst_3104_, v_inst_3105_, v_id_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object* v_text_3108_, lean_object* v_hoverLine_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_){
_start:
{
if (lean_obj_tag(v_x_3111_) == 9)
{
lean_object* v_i_3113_; lean_object* v___x_3114_; 
v_i_3113_ = lean_ctor_get(v_x_3111_, 0);
v___x_3114_ = l_Lean_Elab_Info_pos_x3f(v_x_3111_);
if (lean_obj_tag(v___x_3114_) == 1)
{
lean_object* v_val_3115_; lean_object* v___x_3116_; 
v_val_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = l_Lean_Elab_Info_tailPos_x3f(v_x_3111_);
if (lean_obj_tag(v___x_3116_) == 1)
{
lean_object* v_val_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3132_; 
v_val_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3132_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_val_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3132_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v_line_3122_; uint8_t v___x_3123_; 
lean_inc_ref(v_text_3108_);
v___x_3121_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3108_, v_val_3115_);
lean_dec(v_val_3115_);
v_line_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_line_3122_);
lean_dec_ref(v___x_3121_);
v___x_3123_ = lean_nat_dec_le(v_line_3122_, v_hoverLine_3109_);
lean_dec(v_line_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; 
lean_del_object(v___x_3119_);
lean_dec(v_val_3117_);
lean_dec_ref(v_text_3108_);
v___x_3124_ = lean_box(0);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; lean_object* v_line_3126_; uint8_t v___x_3127_; 
v___x_3125_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3108_, v_val_3117_);
lean_dec(v_val_3117_);
v_line_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_line_3126_);
lean_dec_ref(v___x_3125_);
v___x_3127_ = lean_nat_dec_le(v_hoverLine_3109_, v_line_3126_);
lean_dec(v_line_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
lean_del_object(v___x_3119_);
v___x_3128_ = lean_box(0);
return v___x_3128_;
}
else
{
lean_object* v___x_3130_; 
lean_inc_ref(v_i_3113_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v_i_3113_);
v___x_3130_ = v___x_3119_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_i_3113_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
else
{
lean_object* v___x_3133_; 
lean_dec(v___x_3116_);
lean_dec(v_val_3115_);
lean_dec_ref(v_text_3108_);
v___x_3133_ = lean_box(0);
return v___x_3133_;
}
}
else
{
lean_object* v___x_3134_; 
lean_dec(v___x_3114_);
lean_dec_ref(v_text_3108_);
v___x_3134_ = lean_box(0);
return v___x_3134_;
}
}
else
{
lean_object* v___x_3135_; 
lean_dec_ref(v_text_3108_);
v___x_3135_ = lean_box(0);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object* v_text_3136_, lean_object* v_hoverLine_3137_, lean_object* v_x_3138_, lean_object* v_x_3139_, lean_object* v_x_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Widget_widgetInfosAt_x3f___lam__0(v_text_3136_, v_hoverLine_3137_, v_x_3138_, v_x_3139_, v_x_3140_);
lean_dec_ref(v_x_3140_);
lean_dec_ref(v_x_3139_);
lean_dec_ref(v_x_3138_);
lean_dec(v_hoverLine_3137_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object* v_text_3142_, lean_object* v_t_3143_, lean_object* v_hoverLine_3144_){
_start:
{
lean_object* v___f_3145_; lean_object* v___x_3146_; 
v___f_3145_ = lean_alloc_closure((void*)(l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_3145_, 0, v_text_3142_);
lean_closure_set(v___f_3145_, 1, v_hoverLine_3144_);
v___x_3146_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3145_, v_t_3143_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object* v_j_3147_, lean_object* v_k_3148_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = l_Lean_Json_getObjValD(v_j_3147_, v_k_3148_);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object* v_j_3151_, lean_object* v_k_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_j_3151_, v_k_3152_);
lean_dec_ref(v_k_3152_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 0)
{
lean_object* v___x_3157_; 
v___x_3157_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0));
return v___x_3157_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_x_3156_);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object* v_j_3160_, lean_object* v_k_3161_){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = l_Lean_Json_getObjValD(v_j_3160_, v_k_3161_);
v___x_3163_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object* v_j_3164_, lean_object* v_k_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_j_3164_, v_k_3165_);
lean_dec_ref(v_k_3165_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object* v_json_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v_a_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v_a_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_a_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
v___x_3172_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc_n(v_json_3171_, 4);
v___x_3173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3171_, v___x_3172_);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3176_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3171_, v___x_3175_);
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3179_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3171_, v___x_3178_);
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3182_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3171_, v___x_3181_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3171_, v___x_3184_);
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3190_, 0, v_a_3174_);
lean_ctor_set(v___x_3190_, 1, v_a_3177_);
lean_ctor_set(v___x_3190_, 2, v_a_3180_);
lean_ctor_set(v___x_3190_, 3, v_a_3183_);
lean_ctor_set(v___x_3190_, 4, v_a_3186_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(lean_object* v_k_3197_, lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 0)
{
lean_object* v___x_3199_; 
lean_dec_ref(v_k_3197_);
v___x_3199_ = lean_box(0);
return v___x_3199_;
}
else
{
lean_object* v_val_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_val_3200_ = lean_ctor_get(v_x_3198_, 0);
lean_inc(v_val_3200_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_k_3197_);
lean_ctor_set(v___x_3201_, 1, v_val_3200_);
v___x_3202_ = lean_box(0);
v___x_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3201_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0___boxed(lean_object* v_k_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v_k_3204_, v_x_3205_);
lean_dec(v_x_3205_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(lean_object* v_x_3207_){
_start:
{
lean_object* v_id_3208_; lean_object* v_javascriptHash_3209_; lean_object* v_props_3210_; lean_object* v_range_x3f_3211_; lean_object* v_name_x3f_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_id_3208_ = lean_ctor_get(v_x_3207_, 0);
v_javascriptHash_3209_ = lean_ctor_get(v_x_3207_, 1);
v_props_3210_ = lean_ctor_get(v_x_3207_, 2);
v_range_x3f_3211_ = lean_ctor_get(v_x_3207_, 3);
v_name_x3f_3212_ = lean_ctor_get(v_x_3207_, 4);
v___x_3213_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_id_3208_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v_id_3208_);
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_javascriptHash_3209_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v_javascriptHash_3209_);
v___x_3219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v___x_3215_);
v___x_3220_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_props_3210_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v_props_3210_);
v___x_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v___x_3215_);
v___x_3223_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3224_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v___x_3223_, v_range_x3f_3211_);
v___x_3225_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3226_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v___x_3225_, v_name_x3f_3212_);
v___x_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set(v___x_3227_, 1, v___x_3215_);
v___x_3228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3224_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3222_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3219_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3216_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3233_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3231_, v___x_3232_);
v___x_3234_ = l_Lean_Json_mkObj(v___x_3233_);
lean_dec(v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39____boxed(lean_object* v_x_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(v_x_3235_);
lean_dec_ref(v_x_3235_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_toWidgetInstance_3241_; lean_object* v_range_x3f_3242_; lean_object* v_name_x3f_3243_; lean_object* v_id_3244_; uint64_t v_javascriptHash_3245_; lean_object* v_props_3246_; lean_object* v___x_3247_; lean_object* v_fst_3248_; lean_object* v_snd_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3289_; 
v_toWidgetInstance_3241_ = lean_ctor_get(v_a_3239_, 0);
lean_inc_ref(v_toWidgetInstance_3241_);
v_range_x3f_3242_ = lean_ctor_get(v_a_3239_, 1);
lean_inc(v_range_x3f_3242_);
v_name_x3f_3243_ = lean_ctor_get(v_a_3239_, 2);
lean_inc(v_name_x3f_3243_);
lean_dec_ref(v_a_3239_);
v_id_3244_ = lean_ctor_get(v_toWidgetInstance_3241_, 0);
lean_inc(v_id_3244_);
v_javascriptHash_3245_ = lean_ctor_get_uint64(v_toWidgetInstance_3241_, sizeof(void*)*2);
v_props_3246_ = lean_ctor_get(v_toWidgetInstance_3241_, 1);
lean_inc_ref(v_props_3246_);
lean_dec_ref(v_toWidgetInstance_3241_);
v___x_3247_ = lean_apply_1(v_props_3246_, v_a_3240_);
v_fst_3248_ = lean_ctor_get(v___x_3247_, 0);
v_snd_3249_ = lean_ctor_get(v___x_3247_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3251_ = v___x_3247_;
v_isShared_3252_ = v_isSharedCheck_3289_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_snd_3249_);
lean_inc(v_fst_3248_);
lean_dec(v___x_3247_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3289_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___y_3259_; lean_object* v_fst_3260_; lean_object* v_snd_3261_; lean_object* v_fst_3268_; 
v___x_3253_ = 1;
v___x_3254_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3244_, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
v___x_3256_ = lean_uint64_to_nat(v_javascriptHash_3245_);
v___x_3257_ = l_Lean_bignumToJson(v___x_3256_);
if (lean_obj_tag(v_range_x3f_3242_) == 0)
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_box(0);
v_fst_3268_ = v___x_3279_;
goto v___jp_3267_;
}
else
{
lean_object* v_val_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3288_; 
v_val_3280_ = lean_ctor_get(v_range_x3f_3242_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_range_x3f_3242_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3282_ = v_range_x3f_3242_;
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_val_3280_);
lean_dec(v_range_x3f_3242_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3284_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_3280_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3284_);
v___x_3286_ = v___x_3282_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
v_fst_3268_ = v___x_3286_;
goto v___jp_3267_;
}
}
}
v___jp_3258_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3255_);
lean_ctor_set(v___x_3262_, 1, v___x_3257_);
lean_ctor_set(v___x_3262_, 2, v_fst_3248_);
lean_ctor_set(v___x_3262_, 3, v___y_3259_);
lean_ctor_set(v___x_3262_, 4, v_fst_3260_);
v___x_3263_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(v___x_3262_);
lean_dec_ref_known(v___x_3262_, 5);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v_snd_3261_);
lean_ctor_set(v___x_3251_, 0, v___x_3263_);
v___x_3265_ = v___x_3251_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_snd_3261_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
v___jp_3267_:
{
if (lean_obj_tag(v_name_x3f_3243_) == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_box(0);
v___y_3259_ = v_fst_3268_;
v_fst_3260_ = v___x_3269_;
v_snd_3261_ = v_snd_3249_;
goto v___jp_3258_;
}
else
{
lean_object* v_val_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3278_; 
v_val_3270_ = lean_ctor_get(v_name_x3f_3243_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_name_x3f_3243_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3272_ = v_name_x3f_3243_;
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_val_3270_);
lean_dec(v_name_x3f_3243_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_val_3270_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3274_);
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
v___y_3259_ = v_fst_3268_;
v_fst_3260_ = v___x_3276_;
v_snd_3261_ = v_snd_3249_;
goto v___jp_3258_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_props_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v_props_3290_);
lean_ctor_set(v___x_3292_, 1, v___y_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(v_j_3293_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v_id_3304_; lean_object* v_javascriptHash_3305_; lean_object* v_props_3306_; lean_object* v_range_x3f_3307_; lean_object* v_name_x3f_3308_; lean_object* v___x_3309_; 
v_a_3303_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3294_, 1);
v_id_3304_ = lean_ctor_get(v_a_3303_, 0);
lean_inc(v_id_3304_);
v_javascriptHash_3305_ = lean_ctor_get(v_a_3303_, 1);
lean_inc(v_javascriptHash_3305_);
v_props_3306_ = lean_ctor_get(v_a_3303_, 2);
lean_inc(v_props_3306_);
v_range_x3f_3307_ = lean_ctor_get(v_a_3303_, 3);
lean_inc(v_range_x3f_3307_);
v_name_x3f_3308_ = lean_ctor_get(v_a_3303_, 4);
lean_inc(v_name_x3f_3308_);
lean_dec(v_a_3303_);
v___x_3309_ = l_Lean_Name_fromJson_x3f(v_id_3304_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_name_x3f_3308_);
lean_dec(v_range_x3f_3307_);
lean_dec(v_props_3306_);
lean_dec(v_javascriptHash_3305_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3319_; 
v_a_3318_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3309_, 1);
v___x_3319_ = l_Lean_UInt64_fromJson_x3f(v_javascriptHash_3305_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_a_3318_);
lean_dec(v_name_x3f_3308_);
lean_dec(v_range_x3f_3307_);
lean_dec(v_props_3306_);
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3382_; 
v_a_3328_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3330_ = v___x_3319_;
v_isShared_3331_ = v_isSharedCheck_3382_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3319_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3382_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___f_3332_; lean_object* v___y_3334_; lean_object* v_____do__lift_3335_; lean_object* v_____do__lift_3343_; 
v___f_3332_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_), 2, 1);
lean_closure_set(v___f_3332_, 0, v_props_3306_);
if (lean_obj_tag(v_range_x3f_3307_) == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_box(0);
v_____do__lift_3343_ = v___x_3363_;
goto v___jp_3342_;
}
else
{
lean_object* v_val_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3381_; 
v_val_3364_ = lean_ctor_get(v_range_x3f_3307_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_range_x3f_3307_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3366_ = v_range_x3f_3307_;
v_isShared_3367_ = v_isSharedCheck_3381_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_val_3364_);
lean_dec(v_range_x3f_3307_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3381_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_3364_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_del_object(v___x_3366_);
lean_dec_ref(v___f_3332_);
lean_del_object(v___x_3330_);
lean_dec(v_a_3328_);
lean_dec(v_a_3318_);
lean_dec(v_name_x3f_3308_);
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; 
v_a_3377_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3368_, 1);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_a_3377_);
v___x_3379_ = v___x_3366_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
v_____do__lift_3343_ = v___x_3379_;
goto v___jp_3342_;
}
}
}
}
v___jp_3333_:
{
lean_object* v___x_3336_; uint64_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3336_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3336_, 0, v_a_3318_);
lean_ctor_set(v___x_3336_, 1, v___f_3332_);
v___x_3337_ = lean_unbox_uint64(v_a_3328_);
lean_dec(v_a_3328_);
lean_ctor_set_uint64(v___x_3336_, sizeof(void*)*2, v___x_3337_);
v___x_3338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___y_3334_);
lean_ctor_set(v___x_3338_, 2, v_____do__lift_3335_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3338_);
v___x_3340_ = v___x_3330_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
v___jp_3342_:
{
if (lean_obj_tag(v_name_x3f_3308_) == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_box(0);
v___y_3334_ = v_____do__lift_3343_;
v_____do__lift_3335_ = v___x_3344_;
goto v___jp_3333_;
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3362_; 
v_val_3345_ = lean_ctor_get(v_name_x3f_3308_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_name_x3f_3308_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3347_ = v_name_x3f_3308_;
v_isShared_3348_ = v_isSharedCheck_3362_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_val_3345_);
lean_dec(v_name_x3f_3308_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3362_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Json_getStr_x3f(v_val_3345_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_del_object(v___x_3347_);
lean_dec(v_____do__lift_3343_);
lean_dec_ref(v___f_3332_);
lean_del_object(v___x_3330_);
lean_dec(v_a_3328_);
lean_dec(v_a_3318_);
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3349_, 1);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v_a_3358_);
v___x_3360_ = v___x_3347_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
v___y_3334_ = v_____do__lift_3343_;
v_____do__lift_3335_ = v___x_3360_;
goto v___jp_3333_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object* v_j_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3386_, v_a_3387_);
lean_dec_ref(v_a_3387_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object* v_json_3396_){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
v___x_3397_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3398_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3396_, v___x_3397_);
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(lean_object* v_x_3409_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3410_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v_x_3409_);
v___x_3412_ = lean_box(0);
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___x_3412_);
v___x_3415_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3416_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3414_, v___x_3415_);
v___x_3417_ = l_Lean_Json_mkObj(v___x_3416_);
lean_dec(v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t v_sz_3420_, size_t v_i_3421_, lean_object* v_bs_3422_){
_start:
{
uint8_t v___x_3423_; 
v___x_3423_ = lean_usize_dec_lt(v_i_3421_, v_sz_3420_);
if (v___x_3423_ == 0)
{
return v_bs_3422_;
}
else
{
lean_object* v_v_3424_; lean_object* v___x_3425_; lean_object* v_bs_x27_3426_; size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v_v_3424_ = lean_array_uget(v_bs_3422_, v_i_3421_);
v___x_3425_ = lean_unsigned_to_nat(0u);
v_bs_x27_3426_ = lean_array_uset(v_bs_3422_, v_i_3421_, v___x_3425_);
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3421_, v___x_3427_);
v___x_3429_ = lean_array_uset(v_bs_x27_3426_, v_i_3421_, v_v_3424_);
v_i_3421_ = v___x_3428_;
v_bs_3422_ = v___x_3429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object* v_sz_3431_, lean_object* v_i_3432_, lean_object* v_bs_3433_){
_start:
{
size_t v_sz_boxed_3434_; size_t v_i_boxed_3435_; lean_object* v_res_3436_; 
v_sz_boxed_3434_ = lean_unbox_usize(v_sz_3431_);
lean_dec(v_sz_3431_);
v_i_boxed_3435_ = lean_unbox_usize(v_i_3432_);
lean_dec(v_i_3432_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_boxed_3434_, v_i_boxed_3435_, v_bs_3433_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object* v_a_3437_){
_start:
{
size_t v_sz_3438_; size_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_sz_3438_ = lean_array_size(v_a_3437_);
v___x_3439_ = ((size_t)0ULL);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3438_, v___x_3439_, v_a_3437_);
v___x_3441_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_bs_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_bs_3444_);
lean_ctor_set(v___x_3447_, 1, v___y_3445_);
return v___x_3447_;
}
else
{
lean_object* v_v_3448_; lean_object* v___x_3449_; lean_object* v_fst_3450_; lean_object* v_snd_3451_; lean_object* v___x_3452_; lean_object* v_bs_x27_3453_; size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v_v_3448_ = lean_array_uget_borrowed(v_bs_3444_, v_i_3443_);
lean_inc(v_v_3448_);
v___x_3449_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3448_, v___y_3445_);
v_fst_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_fst_3450_);
v_snd_3451_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_snd_3451_);
lean_dec_ref(v___x_3449_);
v___x_3452_ = lean_unsigned_to_nat(0u);
v_bs_x27_3453_ = lean_array_uset(v_bs_3444_, v_i_3443_, v___x_3452_);
v___x_3454_ = ((size_t)1ULL);
v___x_3455_ = lean_usize_add(v_i_3443_, v___x_3454_);
v___x_3456_ = lean_array_uset(v_bs_x27_3453_, v_i_3443_, v_fst_3450_);
v_i_3443_ = v___x_3455_;
v_bs_3444_ = v___x_3456_;
v___y_3445_ = v_snd_3451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object* v_sz_3458_, lean_object* v_i_3459_, lean_object* v_bs_3460_, lean_object* v___y_3461_){
_start:
{
size_t v_sz_boxed_3462_; size_t v_i_boxed_3463_; lean_object* v_res_3464_; 
v_sz_boxed_3462_ = lean_unbox_usize(v_sz_3458_);
lean_dec(v_sz_3458_);
v_i_boxed_3463_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_boxed_3462_, v_i_boxed_3463_, v_bs_3460_, v___y_3461_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
size_t v_sz_3467_; size_t v___x_3468_; lean_object* v___x_3469_; lean_object* v_fst_3470_; lean_object* v_snd_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3480_; 
v_sz_3467_ = lean_array_size(v_a_3465_);
v___x_3468_ = ((size_t)0ULL);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3467_, v___x_3468_, v_a_3465_, v_a_3466_);
v_fst_3470_ = lean_ctor_get(v___x_3469_, 0);
v_snd_3471_ = lean_ctor_get(v___x_3469_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3473_ = v___x_3469_;
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_snd_3471_);
lean_inc(v_fst_3470_);
lean_dec(v___x_3469_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3475_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_fst_3470_);
v___x_3476_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(v___x_3475_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3476_);
v___x_3478_ = v___x_3473_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_snd_3471_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t v_sz_3481_, size_t v_i_3482_, lean_object* v_bs_3483_){
_start:
{
uint8_t v___x_3484_; 
v___x_3484_ = lean_usize_dec_lt(v_i_3482_, v_sz_3481_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_bs_3483_);
return v___x_3485_;
}
else
{
lean_object* v_v_3486_; lean_object* v___x_3487_; 
v_v_3486_ = lean_array_uget_borrowed(v_bs_3483_, v_i_3482_);
lean_inc(v_v_3486_);
v___x_3487_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref(v_bs_3483_);
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v_bs_x27_3498_; size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v_a_3496_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3497_ = lean_unsigned_to_nat(0u);
v_bs_x27_3498_ = lean_array_uset(v_bs_3483_, v_i_3482_, v___x_3497_);
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3482_, v___x_3499_);
v___x_3501_ = lean_array_uset(v_bs_x27_3498_, v_i_3482_, v_a_3496_);
v_i_3482_ = v___x_3500_;
v_bs_3483_ = v___x_3501_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object* v_sz_3503_, lean_object* v_i_3504_, lean_object* v_bs_3505_){
_start:
{
size_t v_sz_boxed_3506_; size_t v_i_boxed_3507_; lean_object* v_res_3508_; 
v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3503_);
lean_dec(v_sz_3503_);
v_i_boxed_3507_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_boxed_3506_, v_i_boxed_3507_, v_bs_3505_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t v_sz_3509_, size_t v_i_3510_, lean_object* v_bs_3511_){
_start:
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_usize_dec_lt(v_i_3510_, v_sz_3509_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_bs_3511_);
return v___x_3513_;
}
else
{
lean_object* v_v_3514_; lean_object* v___x_3515_; lean_object* v_bs_x27_3516_; size_t v___x_3517_; size_t v___x_3518_; lean_object* v___x_3519_; 
v_v_3514_ = lean_array_uget(v_bs_3511_, v_i_3510_);
v___x_3515_ = lean_unsigned_to_nat(0u);
v_bs_x27_3516_ = lean_array_uset(v_bs_3511_, v_i_3510_, v___x_3515_);
v___x_3517_ = ((size_t)1ULL);
v___x_3518_ = lean_usize_add(v_i_3510_, v___x_3517_);
v___x_3519_ = lean_array_uset(v_bs_x27_3516_, v_i_3510_, v_v_3514_);
v_i_3510_ = v___x_3518_;
v_bs_3511_ = v___x_3519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_sz_3521_, lean_object* v_i_3522_, lean_object* v_bs_3523_){
_start:
{
size_t v_sz_boxed_3524_; size_t v_i_boxed_3525_; lean_object* v_res_3526_; 
v_sz_boxed_3524_ = lean_unbox_usize(v_sz_3521_);
lean_dec(v_sz_3521_);
v_i_boxed_3525_ = lean_unbox_usize(v_i_3522_);
lean_dec(v_i_3522_);
v_res_3526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_3524_, v_i_boxed_3525_, v_bs_3523_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object* v_x_3528_){
_start:
{
if (lean_obj_tag(v_x_3528_) == 4)
{
lean_object* v_elems_3529_; size_t v_sz_3530_; size_t v___x_3531_; lean_object* v___x_3532_; 
v_elems_3529_ = lean_ctor_get(v_x_3528_, 0);
lean_inc_ref(v_elems_3529_);
lean_dec_ref_known(v_x_3528_, 1);
v_sz_3530_ = lean_array_size(v_elems_3529_);
v___x_3531_ = ((size_t)0ULL);
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3530_, v___x_3531_, v_elems_3529_);
return v___x_3532_;
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3533_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0));
v___x_3534_ = lean_unsigned_to_nat(80u);
v___x_3535_ = l_Lean_Json_pretty(v_x_3528_, v___x_3534_);
v___x_3536_ = lean_string_append(v___x_3533_, v___x_3535_);
lean_dec_ref(v___x_3535_);
v___x_3537_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v___x_3538_ = lean_string_append(v___x_3536_, v___x_3537_);
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
return v___x_3539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_j_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(v_j_3540_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3542_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3542_, 1);
v___x_3552_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_a_3551_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3561_; size_t v_sz_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v_a_3561_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3552_, 1);
v_sz_3562_ = lean_array_size(v_a_3561_);
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3562_, v___x_3563_, v_a_3561_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_a_3573_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3564_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3564_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object* v_j_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_j_3581_, v_a_3582_);
lean_dec_ref(v_a_3582_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t v_sz_3584_, size_t v_i_3585_, lean_object* v_bs_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3584_, v_i_3585_, v_bs_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object* v_sz_3589_, lean_object* v_i_3590_, lean_object* v_bs_3591_, lean_object* v___y_3592_){
_start:
{
size_t v_sz_boxed_3593_; size_t v_i_boxed_3594_; lean_object* v_res_3595_; 
v_sz_boxed_3593_ = lean_unbox_usize(v_sz_3589_);
lean_dec(v_sz_3589_);
v_i_boxed_3594_ = lean_unbox_usize(v_i_3590_);
lean_dec(v_i_3590_);
v_res_3595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_boxed_3593_, v_i_boxed_3594_, v_bs_3591_, v___y_3592_);
lean_dec_ref(v___y_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object* v_x_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
if (lean_obj_tag(v_x_3602_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v_x_3602_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v_x_3602_, 1);
v___x_3609_ = l_Lean_stringToMessageData(v_a_3608_);
v___x_3610_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_3609_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
return v___x_3610_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_a_3611_ = lean_ctor_get(v_x_3602_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v_x_3602_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v_x_3602_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 0);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object* v_x_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object* v_id_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v_env_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3632_ = lean_st_ref_get(v___y_3630_);
v_env_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc_ref(v_env_3633_);
lean_dec(v___x_3632_);
v___x_3634_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3629_);
v___x_3635_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3636_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3633_, v___x_3634_, v___x_3635_, v_id_3626_);
lean_dec_ref(v___x_3634_);
v___x_3637_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v___x_3636_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object* v_id_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object* v___x_3645_, size_t v_sz_3646_, size_t v_i_3647_, lean_object* v_bs_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_usize_dec_lt(v_i_3647_, v_sz_3646_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
lean_dec_ref(v___x_3645_);
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_bs_3648_);
return v___x_3655_;
}
else
{
lean_object* v_v_3656_; lean_object* v_id_3657_; lean_object* v___x_3658_; lean_object* v_bs_x27_3659_; lean_object* v_a_3661_; lean_object* v___y_3671_; uint8_t v___x_3692_; lean_object* v___x_3693_; 
v_v_3656_ = lean_array_uget(v_bs_3648_, v_i_3647_);
v_id_3657_ = lean_ctor_get(v_v_3656_, 0);
v___x_3658_ = lean_unsigned_to_nat(0u);
v_bs_x27_3659_ = lean_array_uset(v_bs_3648_, v_i_3647_, v___x_3658_);
v___x_3692_ = 0;
lean_inc(v_id_3657_);
lean_inc_ref(v___x_3645_);
v___x_3693_ = l_Lean_Environment_find_x3f(v___x_3645_, v_id_3657_, v___x_3692_);
if (lean_obj_tag(v___x_3693_) == 0)
{
v___y_3671_ = v___x_3693_;
goto v___jp_3670_;
}
else
{
lean_object* v_val_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; 
v_val_3694_ = lean_ctor_get(v___x_3693_, 0);
v___x_3695_ = l_Lean_ConstantInfo_type(v_val_3694_);
v___x_3696_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3697_ = l_Lean_Expr_isConstOf(v___x_3695_, v___x_3696_);
lean_dec_ref(v___x_3695_);
if (v___x_3697_ == 0)
{
lean_dec_ref_known(v___x_3693_, 1);
goto v___jp_3668_;
}
else
{
v___y_3671_ = v___x_3693_;
goto v___jp_3670_;
}
}
v___jp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3662_ = lean_box(0);
v___x_3663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3663_, 0, v_v_3656_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
lean_ctor_set(v___x_3663_, 2, v_a_3661_);
v___x_3664_ = ((size_t)1ULL);
v___x_3665_ = lean_usize_add(v_i_3647_, v___x_3664_);
v___x_3666_ = lean_array_uset(v_bs_x27_3659_, v_i_3647_, v___x_3663_);
v_i_3647_ = v___x_3665_;
v_bs_3648_ = v___x_3666_;
goto _start;
}
v___jp_3668_:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_box(0);
v_a_3661_ = v___x_3669_;
goto v___jp_3660_;
}
v___jp_3670_:
{
if (lean_obj_tag(v___y_3671_) == 0)
{
goto v___jp_3668_;
}
else
{
lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3690_; 
v_isSharedCheck_3690_ = !lean_is_exclusive(v___y_3671_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v___y_3671_, 0);
lean_dec(v_unused_3691_);
v___x_3673_ = v___y_3671_;
v_isShared_3674_ = v_isSharedCheck_3690_;
goto v_resetjp_3672_;
}
else
{
lean_dec(v___y_3671_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3690_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_id_3675_; lean_object* v___x_3676_; 
v_id_3675_ = lean_ctor_get(v_v_3656_, 0);
lean_inc(v_id_3675_);
v___x_3676_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3675_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v_name_3678_; lean_object* v___x_3680_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v_name_3678_ = lean_ctor_get(v_a_3677_, 0);
lean_inc_ref(v_name_3678_);
lean_dec(v_a_3677_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_name_3678_);
v___x_3680_ = v___x_3673_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_name_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
v_a_3661_ = v___x_3680_;
goto v___jp_3660_;
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_del_object(v___x_3673_);
lean_dec_ref(v_bs_x27_3659_);
lean_dec(v_v_3656_);
lean_dec_ref(v___x_3645_);
v_a_3682_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3676_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3676_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object* v___x_3698_, lean_object* v_sz_3699_, lean_object* v_i_3700_, lean_object* v_bs_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
size_t v_sz_boxed_3707_; size_t v_i_boxed_3708_; lean_object* v_res_3709_; 
v_sz_boxed_3707_ = lean_unbox_usize(v_sz_3699_);
lean_dec(v_sz_3699_);
v_i_boxed_3708_ = lean_unbox_usize(v_i_3700_);
lean_dec(v_i_3700_);
v_res_3709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3698_, v_sz_boxed_3707_, v_i_boxed_3708_, v_bs_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object* v___x_3710_, lean_object* v___x_3711_, size_t v_sz_3712_, size_t v_i_3713_, lean_object* v_bs_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_usize_dec_lt(v_i_3713_, v_sz_3712_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
lean_dec_ref(v___x_3711_);
lean_dec_ref(v___x_3710_);
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v_bs_3714_);
return v___x_3721_;
}
else
{
lean_object* v_v_3722_; lean_object* v_toWidgetInstance_3723_; lean_object* v_stx_3724_; lean_object* v_id_3725_; lean_object* v___x_3726_; lean_object* v_bs_x27_3727_; lean_object* v___y_3729_; lean_object* v___y_3730_; uint8_t v___x_3736_; lean_object* v_a_3738_; lean_object* v___y_3753_; lean_object* v___x_3773_; 
v_v_3722_ = lean_array_uget_borrowed(v_bs_3714_, v_i_3713_);
v_toWidgetInstance_3723_ = lean_ctor_get(v_v_3722_, 0);
lean_inc_ref(v_toWidgetInstance_3723_);
v_stx_3724_ = lean_ctor_get(v_v_3722_, 1);
lean_inc(v_stx_3724_);
v_id_3725_ = lean_ctor_get(v_toWidgetInstance_3723_, 0);
v___x_3726_ = lean_unsigned_to_nat(0u);
v_bs_x27_3727_ = lean_array_uset(v_bs_3714_, v_i_3713_, v___x_3726_);
v___x_3736_ = 0;
lean_inc(v_id_3725_);
lean_inc_ref(v___x_3711_);
v___x_3773_ = l_Lean_Environment_find_x3f(v___x_3711_, v_id_3725_, v___x_3736_);
if (lean_obj_tag(v___x_3773_) == 0)
{
v___y_3753_ = v___x_3773_;
goto v___jp_3752_;
}
else
{
lean_object* v_val_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_val_3774_ = lean_ctor_get(v___x_3773_, 0);
v___x_3775_ = l_Lean_ConstantInfo_type(v_val_3774_);
v___x_3776_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3777_ = l_Lean_Expr_isConstOf(v___x_3775_, v___x_3776_);
lean_dec_ref(v___x_3775_);
if (v___x_3777_ == 0)
{
lean_dec_ref_known(v___x_3773_, 1);
goto v___jp_3750_;
}
else
{
v___y_3753_ = v___x_3773_;
goto v___jp_3752_;
}
}
v___jp_3728_:
{
lean_object* v___x_3731_; size_t v___x_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3731_, 0, v_toWidgetInstance_3723_);
lean_ctor_set(v___x_3731_, 1, v___y_3730_);
lean_ctor_set(v___x_3731_, 2, v___y_3729_);
v___x_3732_ = ((size_t)1ULL);
v___x_3733_ = lean_usize_add(v_i_3713_, v___x_3732_);
v___x_3734_ = lean_array_uset(v_bs_x27_3727_, v_i_3713_, v___x_3731_);
v_i_3713_ = v___x_3733_;
v_bs_3714_ = v___x_3734_;
goto _start;
}
v___jp_3737_:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Syntax_getRange_x3f(v_stx_3724_, v___x_3736_);
lean_dec(v_stx_3724_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_box(0);
v___y_3729_ = v_a_3738_;
v___y_3730_ = v___x_3740_;
goto v___jp_3728_;
}
else
{
lean_object* v_val_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3749_; 
v_val_3741_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3743_ = v___x_3739_;
v_isShared_3744_ = v_isSharedCheck_3749_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_val_3741_);
lean_dec(v___x_3739_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3749_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_inc_ref(v___x_3710_);
v___x_3745_ = l_Lean_Syntax_Range_toLspRange(v___x_3710_, v_val_3741_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3745_);
v___x_3747_ = v___x_3743_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
v___y_3729_ = v_a_3738_;
v___y_3730_ = v___x_3747_;
goto v___jp_3728_;
}
}
}
}
v___jp_3750_:
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_box(0);
v_a_3738_ = v___x_3751_;
goto v___jp_3737_;
}
v___jp_3752_:
{
if (lean_obj_tag(v___y_3753_) == 0)
{
goto v___jp_3750_;
}
else
{
lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3771_; 
v_isSharedCheck_3771_ = !lean_is_exclusive(v___y_3753_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___y_3753_, 0);
lean_dec(v_unused_3772_);
v___x_3755_ = v___y_3753_;
v_isShared_3756_ = v_isSharedCheck_3771_;
goto v_resetjp_3754_;
}
else
{
lean_dec(v___y_3753_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3771_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; 
lean_inc(v_id_3725_);
v___x_3757_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3725_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v_name_3759_; lean_object* v___x_3761_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v_name_3759_ = lean_ctor_get(v_a_3758_, 0);
lean_inc_ref(v_name_3759_);
lean_dec(v_a_3758_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v_name_3759_);
v___x_3761_ = v___x_3755_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_name_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
v_a_3738_ = v___x_3761_;
goto v___jp_3737_;
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_del_object(v___x_3755_);
lean_dec_ref(v_bs_x27_3727_);
lean_dec(v_stx_3724_);
lean_dec_ref(v_toWidgetInstance_3723_);
lean_dec_ref(v___x_3711_);
lean_dec_ref(v___x_3710_);
v_a_3763_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3757_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3757_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object* v___x_3778_, lean_object* v___x_3779_, lean_object* v_sz_3780_, lean_object* v_i_3781_, lean_object* v_bs_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
size_t v_sz_boxed_3788_; size_t v_i_boxed_3789_; lean_object* v_res_3790_; 
v_sz_boxed_3788_ = lean_unbox_usize(v_sz_3780_);
lean_dec(v_sz_3780_);
v_i_boxed_3789_ = lean_unbox_usize(v_i_3781_);
lean_dec(v_i_3781_);
v_res_3790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3778_, v___x_3779_, v_sz_boxed_3788_, v_i_boxed_3789_, v_bs_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object* v_pos_3791_, lean_object* v_text_3792_, lean_object* v_val_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; lean_object* v_env_3800_; lean_object* v___x_3801_; 
v___x_3799_ = lean_st_ref_get(v___y_3797_);
v_env_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc_ref(v_env_3800_);
lean_dec(v___x_3799_);
v___x_3801_ = l_Lean_Widget_evalPanelWidgets(v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; size_t v_sz_3803_; size_t v___x_3804_; lean_object* v___x_3805_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v_sz_3803_ = lean_array_size(v_a_3802_);
v___x_3804_ = ((size_t)0ULL);
lean_inc_ref(v_env_3800_);
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v_env_3800_, v_sz_3803_, v___x_3804_, v_a_3802_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v_line_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; size_t v_sz_3810_; lean_object* v___x_3811_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v_line_3807_ = lean_ctor_get(v_pos_3791_, 0);
lean_inc(v_line_3807_);
lean_dec_ref(v_pos_3791_);
lean_inc_ref(v_text_3792_);
v___x_3808_ = l_Lean_Widget_widgetInfosAt_x3f(v_text_3792_, v_val_3793_, v_line_3807_);
v___x_3809_ = lean_array_mk(v___x_3808_);
v_sz_3810_ = lean_array_size(v___x_3809_);
v___x_3811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v_text_3792_, v_env_3800_, v_sz_3810_, v___x_3804_, v___x_3809_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3820_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3820_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3820_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3816_ = l_Array_append___redArg(v_a_3806_, v_a_3812_);
lean_dec(v_a_3812_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v___x_3816_);
v___x_3818_ = v___x_3814_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v_a_3806_);
v_a_3821_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3811_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3811_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v_env_3800_);
lean_dec_ref(v_val_3793_);
lean_dec_ref(v_text_3792_);
lean_dec_ref(v_pos_3791_);
v_a_3829_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3805_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3805_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_env_3800_);
lean_dec_ref(v_val_3793_);
lean_dec_ref(v_text_3792_);
lean_dec_ref(v_pos_3791_);
v_a_3837_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3801_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3801_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object* v_pos_3845_, lean_object* v_text_3846_, lean_object* v_val_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3845_, v_text_3846_, v_val_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object* v_pos_3858_, lean_object* v_text_3859_, lean_object* v_x_3860_, lean_object* v___y_3861_){
_start:
{
if (lean_obj_tag(v_x_3860_) == 1)
{
lean_object* v_val_3866_; 
v_val_3866_ = lean_ctor_get(v_x_3860_, 0);
lean_inc(v_val_3866_);
lean_dec_ref_known(v_x_3860_, 1);
if (lean_obj_tag(v_val_3866_) == 0)
{
lean_object* v_i_3867_; 
v_i_3867_ = lean_ctor_get(v_val_3866_, 0);
if (lean_obj_tag(v_i_3867_) == 0)
{
lean_object* v_info_3868_; lean_object* v___f_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_info_3868_ = lean_ctor_get(v_i_3867_, 0);
lean_inc_ref(v_info_3868_);
v___f_3869_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3869_, 0, v_pos_3858_);
lean_closure_set(v___f_3869_, 1, v_text_3859_);
lean_closure_set(v___f_3869_, 2, v_val_3866_);
v___x_3870_ = lean_box(0);
v___x_3871_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__1));
v___x_3872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3872_, 0, v_info_3868_);
lean_ctor_set(v___x_3872_, 1, v___x_3870_);
lean_ctor_set(v___x_3872_, 2, v___x_3871_);
v___x_3873_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_3874_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_3872_, v___x_3873_, v___f_3869_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3891_; 
v_a_3883_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3885_ = v___x_3874_;
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3874_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = l_Lean_Server_RequestError_ofIoError(v_a_3883_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3887_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_dec_ref_known(v_val_3866_, 2);
lean_dec_ref(v_text_3859_);
lean_dec_ref(v_pos_3858_);
goto v___jp_3863_;
}
}
else
{
lean_dec(v_val_3866_);
lean_dec_ref(v_text_3859_);
lean_dec_ref(v_pos_3858_);
goto v___jp_3863_;
}
}
else
{
lean_dec(v_x_3860_);
lean_dec_ref(v_text_3859_);
lean_dec_ref(v_pos_3858_);
goto v___jp_3863_;
}
v___jp_3863_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__0));
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object* v_pos_3892_, lean_object* v_text_3893_, lean_object* v_x_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3892_, v_text_3893_, v_x_3894_, v___y_3895_);
lean_dec_ref(v___y_3895_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets(lean_object* v_pos_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v_a_3902_; lean_object* v_toEditableDocumentCore_3903_; lean_object* v_meta_3904_; lean_object* v_initSnap_3905_; lean_object* v_text_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3901_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_3899_);
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref(v___x_3901_);
v_toEditableDocumentCore_3903_ = lean_ctor_get(v_a_3902_, 0);
lean_inc_ref(v_toEditableDocumentCore_3903_);
lean_dec(v_a_3902_);
v_meta_3904_ = lean_ctor_get(v_toEditableDocumentCore_3903_, 0);
lean_inc_ref(v_meta_3904_);
v_initSnap_3905_ = lean_ctor_get(v_toEditableDocumentCore_3903_, 1);
lean_inc_ref(v_initSnap_3905_);
lean_dec_ref(v_toEditableDocumentCore_3903_);
v_text_3906_ = lean_ctor_get(v_meta_3904_, 3);
lean_inc_ref_n(v_text_3906_, 2);
lean_dec_ref(v_meta_3904_);
lean_inc_ref(v_pos_3898_);
v___f_3907_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3907_, 0, v_pos_3898_);
lean_closure_set(v___f_3907_, 1, v_text_3906_);
v___x_3908_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3906_, v_pos_3898_);
v___x_3909_ = 1;
v___x_3910_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_3905_, v_text_3906_, v___x_3908_, v___x_3909_);
v___x_3911_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3910_, v___f_3907_, v_a_3899_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object* v_pos_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Widget_getWidgets(v_pos_3912_, v_a_3913_);
lean_dec_ref(v_a_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object* v_00_u03b1_3916_, lean_object* v_x_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3924_, lean_object* v_x_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(v_00_u03b1_3924_, v_x_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object* v_val_3932_, lean_object* v___f_3933_, lean_object* v_x_3934_, lean_object* v___y_3935_){
_start:
{
if (lean_obj_tag(v_x_3934_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec_ref(v___f_3933_);
v_a_3937_ = lean_ctor_get(v_x_3934_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_x_3934_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v_x_3934_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v_x_3934_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set_tag(v___x_3939_, 1);
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3961_; 
v_a_3945_ = lean_ctor_get(v_x_3934_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_x_3934_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3947_ = v_x_3934_;
v_isShared_3948_ = v_isSharedCheck_3961_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v_x_3934_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3961_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v_objects_3950_; lean_object* v_expireTime_3951_; lean_object* v___f_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v_fst_3955_; lean_object* v_snd_3956_; lean_object* v___x_3957_; lean_object* v___x_3959_; 
v___x_3949_ = lean_st_ref_take(v_val_3932_);
v_objects_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc_ref(v_objects_3950_);
v_expireTime_3951_ = lean_ctor_get(v___x_3949_, 1);
lean_inc(v_expireTime_3951_);
lean_dec(v___x_3949_);
v___f_3952_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_3952_, 0, v_expireTime_3951_);
v___x_3953_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_a_3945_, v_objects_3950_);
v___x_3954_ = l_Prod_map___redArg(v___f_3933_, v___f_3952_, v___x_3953_);
v_fst_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_fst_3955_);
v_snd_3956_ = lean_ctor_get(v___x_3954_, 1);
lean_inc(v_snd_3956_);
lean_dec_ref(v___x_3954_);
v___x_3957_ = lean_st_ref_put(v_val_3932_, v_snd_3956_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set_tag(v___x_3947_, 0);
lean_ctor_set(v___x_3947_, 0, v_fst_3955_);
v___x_3959_ = v___x_3947_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_fst_3955_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object* v_val_3962_, lean_object* v___f_3963_, lean_object* v_x_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_3962_, v___f_3963_, v_x_3964_, v___y_3965_);
lean_dec_ref(v___y_3965_);
lean_dec(v_val_3962_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object* v___f_3968_, lean_object* v_method_3969_, lean_object* v_handler_3970_, uint64_t v_seshId_3971_, lean_object* v_j_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_rpcSessions_3975_; lean_object* v___x_3976_; 
v_rpcSessions_3975_ = lean_ctor_get(v___y_3973_, 0);
v___x_3976_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_3975_, v_seshId_3971_);
if (lean_obj_tag(v___x_3976_) == 1)
{
lean_object* v_val_3977_; lean_object* v___f_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_val_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc_n(v_val_3977_, 2);
lean_dec_ref_known(v___x_3976_, 1);
v___f_3978_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3978_, 0, v_val_3977_);
lean_closure_set(v___f_3978_, 1, v___f_3968_);
v___x_3979_ = lean_st_ref_get(v_val_3977_);
lean_dec(v_val_3977_);
lean_dec(v___x_3979_);
lean_inc(v_j_3972_);
v___x_3980_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v_j_3972_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v___f_3978_);
lean_dec_ref(v_handler_3970_);
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_4001_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4001_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
uint8_t v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3985_ = 3;
v___x_3986_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_3987_ = 1;
v___x_3988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_3969_, v___x_3987_);
v___x_3989_ = lean_string_append(v___x_3986_, v___x_3988_);
lean_dec_ref(v___x_3988_);
v___x_3990_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_3991_ = lean_string_append(v___x_3989_, v___x_3990_);
v___x_3992_ = l_Lean_Json_compress(v_j_3972_);
v___x_3993_ = lean_string_append(v___x_3991_, v___x_3992_);
lean_dec_ref(v___x_3992_);
v___x_3994_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_3995_ = lean_string_append(v___x_3993_, v___x_3994_);
v___x_3996_ = lean_string_append(v___x_3995_, v_a_3981_);
lean_dec(v_a_3981_);
v___x_3997_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*1, v___x_3985_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set_tag(v___x_3983_, 1);
lean_ctor_set(v___x_3983_, 0, v___x_3997_);
v___x_3999_ = v___x_3983_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4003_; 
lean_dec(v_j_3972_);
lean_dec(v_method_3969_);
v_a_4002_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_3980_, 1);
lean_inc_ref(v___y_3973_);
v___x_4003_ = lean_apply_3(v_handler_3970_, v_a_4002_, v___y_3973_, lean_box(0));
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v___x_4005_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_4004_, v___f_3978_, v___y_3973_);
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec_ref(v___f_3978_);
v_a_4006_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4003_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4003_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec(v___x_3976_);
lean_dec(v_j_3972_);
lean_dec_ref(v_handler_3970_);
lean_dec(v_method_3969_);
lean_dec_ref(v___f_3968_);
v___x_4014_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
return v___x_4015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v___f_4016_, lean_object* v_method_4017_, lean_object* v_handler_4018_, lean_object* v_seshId_4019_, lean_object* v_j_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
uint64_t v_seshId_boxed_4023_; lean_object* v_res_4024_; 
v_seshId_boxed_4023_ = lean_unbox_uint64(v_seshId_4019_);
lean_dec_ref(v_seshId_4019_);
v_res_4024_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v___f_4016_, v_method_4017_, v_handler_4018_, v_seshId_boxed_4023_, v_j_4020_, v___y_4021_);
lean_dec_ref(v___y_4021_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_4025_, lean_object* v_handler_4026_){
_start:
{
lean_object* v___f_4027_; lean_object* v___f_4028_; 
v___f_4027_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_4028_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4028_, 0, v___f_4027_);
lean_closure_set(v___f_4028_, 1, v_method_4025_);
lean_closure_set(v___f_4028_, 2, v_handler_4026_);
return v___f_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object* v_method_4029_, lean_object* v_handler_4030_){
_start:
{
lean_object* v___x_4032_; uint8_t v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v_errMsg_4037_; uint8_t v___x_4038_; 
v___x_4032_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_4033_ = 1;
lean_inc(v_method_4029_);
v___x_4034_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_4029_, v___x_4033_);
v___x_4035_ = lean_string_append(v___x_4032_, v___x_4034_);
lean_dec_ref(v___x_4034_);
v___x_4036_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_4037_ = lean_string_append(v___x_4035_, v___x_4036_);
v___x_4038_ = l_Lean_initializing();
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec_ref(v_handler_4030_);
lean_dec(v_method_4029_);
v___x_4039_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_4040_ = lean_string_append(v_errMsg_4037_, v___x_4039_);
v___x_4041_ = lean_mk_io_user_error(v___x_4040_);
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
return v___x_4042_;
}
else
{
lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; 
v___x_4043_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_4044_ = lean_st_ref_get(v___x_4043_);
v___x_4045_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4044_, v_method_4029_);
lean_dec(v___x_4044_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
lean_dec_ref(v_errMsg_4037_);
lean_inc(v_method_4029_);
v___x_4046_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(v_method_4029_, v_handler_4030_);
v___x_4047_ = lean_st_ref_take(v___x_4043_);
v___x_4048_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4047_, v_method_4029_, v___x_4046_);
v___x_4049_ = lean_st_ref_put(v___x_4043_, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
return v___x_4050_;
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec_ref(v_handler_4030_);
lean_dec(v_method_4029_);
v___x_4051_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_4052_ = lean_string_append(v_errMsg_4037_, v___x_4051_);
v___x_4053_ = lean_mk_io_user_error(v___x_4052_);
v___x_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4055_, lean_object* v_handler_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_4055_, v_handler_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4067_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4068_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v___x_4066_, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
return v_res_4070_;
}
}
lean_object* runtime_initialize_Lean_Elab_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_RequestHandling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Util(builtin);
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
res = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_();
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
lean_object* initialize_Lean_Language_Lean_Util(uint8_t builtin);
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
res = initialize_Lean_Language_Lean_Util(builtin);
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
