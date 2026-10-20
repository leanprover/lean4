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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*);
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
v___x_107_ = lean_nat_add(v___y_104_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___y_104_);
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
lean_ctor_set(v___x_87_, 3, v___y_105_);
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
lean_ctor_set(v_reuseFailAlloc_112_, 3, v___y_105_);
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
v___y_104_ = v___x_119_;
v___y_105_ = v___x_118_;
v___y_106_ = v_size_120_;
goto v___jp_103_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___y_104_ = v___x_119_;
v___y_105_ = v___x_118_;
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
v___x_246_ = lean_nat_add(v___y_243_, v___y_245_);
lean_dec(v___y_245_);
lean_dec(v___y_243_);
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
lean_ctor_set(v___x_226_, 3, v___y_244_);
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
lean_ctor_set(v_reuseFailAlloc_251_, 3, v___y_244_);
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
v___y_243_ = v___x_259_;
v___y_244_ = v___x_258_;
v___y_245_ = v_size_260_;
goto v___jp_242_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___y_243_ = v___x_259_;
v___y_244_ = v___x_258_;
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
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((size_t)0ULL);
v___x_445_ = lean_usize_of_nat(v___x_442_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v___x_441_, v___x_444_, v___x_445_, v_b_433_);
v___y_435_ = v___x_446_;
goto v___jp_434_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_447_, lean_object* v_i_448_, lean_object* v_stop_449_, lean_object* v_b_450_){
_start:
{
size_t v_i_boxed_451_; size_t v_stop_boxed_452_; lean_object* v_res_453_; 
v_i_boxed_451_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_stop_boxed_452_ = lean_unbox_usize(v_stop_449_);
lean_dec(v_stop_449_);
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_as_447_, v_i_boxed_451_, v_stop_boxed_452_, v_b_450_);
lean_dec_ref(v_as_447_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v___x_454_, lean_object* v_xss_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_box(1);
v___x_457_ = lean_array_get_size(v_xss_455_);
v___x_458_ = lean_nat_dec_lt(v___x_454_, v___x_457_);
if (v___x_458_ == 0)
{
return v___x_456_;
}
else
{
size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((size_t)0ULL);
v___x_460_ = lean_usize_of_nat(v___x_457_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_xss_455_, v___x_459_, v___x_460_, v___x_456_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v___x_462_, lean_object* v_xss_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(v___x_462_, v_xss_463_);
lean_dec_ref(v_xss_463_);
lean_dec(v___x_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_));
v___x_506_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
return v_res_508_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_509_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_515_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
lean_ctor_set(v___x_515_, 2, v___x_514_);
lean_ctor_set(v___x_515_, 3, v___x_514_);
lean_ctor_set(v___x_515_, 4, v___x_514_);
lean_ctor_set(v___x_515_, 5, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v_nextMacroScope_521_; lean_object* v_ngen_522_; lean_object* v_auxDeclNGen_523_; lean_object* v_traceState_524_; lean_object* v_recordedDeps_525_; lean_object* v_messages_526_; lean_object* v_infoState_527_; lean_object* v_snapshotTasks_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_554_; 
v___x_520_ = lean_st_ref_take(v___y_518_);
v_nextMacroScope_521_ = lean_ctor_get(v___x_520_, 1);
v_ngen_522_ = lean_ctor_get(v___x_520_, 2);
v_auxDeclNGen_523_ = lean_ctor_get(v___x_520_, 3);
v_traceState_524_ = lean_ctor_get(v___x_520_, 4);
v_recordedDeps_525_ = lean_ctor_get(v___x_520_, 6);
v_messages_526_ = lean_ctor_get(v___x_520_, 7);
v_infoState_527_ = lean_ctor_get(v___x_520_, 8);
v_snapshotTasks_528_ = lean_ctor_get(v___x_520_, 9);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; 
v_unused_555_ = lean_ctor_get(v___x_520_, 5);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v___x_520_, 0);
lean_dec(v_unused_556_);
v___x_530_ = v___x_520_;
v_isShared_531_ = v_isSharedCheck_554_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snapshotTasks_528_);
lean_inc(v_infoState_527_);
lean_inc(v_messages_526_);
lean_inc(v_recordedDeps_525_);
lean_inc(v_traceState_524_);
lean_inc(v_auxDeclNGen_523_);
lean_inc(v_ngen_522_);
lean_inc(v_nextMacroScope_521_);
lean_dec(v___x_520_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_554_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 5, v___x_532_);
lean_ctor_set(v___x_530_, 0, v_env_516_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_env_516_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_nextMacroScope_521_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_ngen_522_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_auxDeclNGen_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_traceState_524_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_recordedDeps_525_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_messages_526_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_infoState_527_);
lean_ctor_set(v_reuseFailAlloc_553_, 9, v_snapshotTasks_528_);
v___x_534_ = v_reuseFailAlloc_553_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_mctx_537_; lean_object* v_zetaDeltaFVarIds_538_; lean_object* v_postponed_539_; lean_object* v_diag_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v___x_535_ = lean_st_ref_put(v___y_518_, v___x_534_);
v___x_536_ = lean_st_ref_take(v___y_517_);
v_mctx_537_ = lean_ctor_get(v___x_536_, 0);
v_zetaDeltaFVarIds_538_ = lean_ctor_get(v___x_536_, 2);
v_postponed_539_ = lean_ctor_get(v___x_536_, 3);
v_diag_540_ = lean_ctor_get(v___x_536_, 4);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_536_, 1);
lean_dec(v_unused_552_);
v___x_542_ = v___x_536_;
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_diag_540_);
lean_inc(v_postponed_539_);
lean_inc(v_zetaDeltaFVarIds_538_);
lean_inc(v_mctx_537_);
lean_dec(v___x_536_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_544_ = lean_box(0);
v___x_545_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_545_);
v___x_547_ = v___x_542_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_mctx_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_zetaDeltaFVarIds_538_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_postponed_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_diag_540_);
v___x_547_ = v_reuseFailAlloc_550_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_st_ref_put(v___y_517_, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_544_);
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec(v___y_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(lean_object* v_env_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_562_, v___y_564_, v___y_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(v_env_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_579_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v___x_580_);
lean_ctor_set(v___x_581_, 4, v___x_579_);
lean_ctor_set(v___x_581_, 5, v___x_579_);
lean_ctor_set(v___x_581_, 6, v___x_579_);
lean_ctor_set(v___x_581_, 7, v___x_579_);
lean_ctor_set(v___x_581_, 8, v___x_579_);
lean_ctor_set(v___x_581_, 9, v___x_579_);
lean_ctor_set(v___x_581_, 10, v___x_579_);
lean_ctor_set(v___x_581_, 11, v___x_578_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(32u);
v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = ((size_t)5ULL);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_unsigned_to_nat(32u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_590_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_586_);
lean_ctor_set(v___x_590_, 3, v___x_586_);
lean_ctor_set_usize(v___x_590_, 4, v___x_585_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_box(1);
v___x_592_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_593_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v_toCold_600_; lean_object* v_env_601_; lean_object* v_options_602_; uint8_t v___x_603_; lean_object* v_env_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_599_ = lean_st_ref_get(v___y_597_);
v_toCold_600_ = lean_ctor_get(v___y_596_, 0);
v_env_601_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_env_601_);
lean_dec(v___x_599_);
v_options_602_ = lean_ctor_get(v_toCold_600_, 2);
v___x_603_ = 0;
v_env_604_ = l_Lean_Environment_setRecordingDeps(v_env_601_, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_606_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_602_);
v___x_607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_607_, 0, v_env_604_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
lean_ctor_set(v___x_607_, 3, v_options_602_);
v___x_608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_msgData_595_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msgData_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_ref_619_; lean_object* v___x_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v_ref_619_ = lean_ctor_get(v___y_616_, 2);
v___x_620_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msg_615_, v___y_616_, v___y_617_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_629_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
lean_inc(v_ref_619_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_ref_619_);
lean_ctor_set(v___x_625_, 1, v_a_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 1);
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_634_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_637_ = l_Lean_stringToMessageData(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v_name_641_, lean_object* v_decl_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_647_ = l_Lean_MessageData_ofName(v_name_641_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v___x_650_, v___y_643_, v___y_644_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_name_652_, lean_object* v_decl_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_name_652_, v_decl_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v_decl_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v_addEntryFn_658_, lean_object* v___x_659_, lean_object* v_s_660_){
_start:
{
lean_object* v_importedEntries_661_; lean_object* v_state_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_importedEntries_661_ = lean_ctor_get(v_s_660_, 0);
v_state_662_ = lean_ctor_get(v_s_660_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_s_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v_s_660_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_state_662_);
lean_inc(v_importedEntries_661_);
lean_dec(v_s_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_state_666_; lean_object* v___x_668_; 
v_state_666_ = lean_apply_2(v_addEntryFn_658_, v_state_662_, v___x_659_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v_state_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_importedEntries_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_state_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_671_, uint64_t v_k_672_){
_start:
{
if (lean_obj_tag(v_t_671_) == 0)
{
lean_object* v_k_673_; lean_object* v_v_674_; lean_object* v_l_675_; lean_object* v_r_676_; uint64_t v___x_677_; uint8_t v___x_678_; 
v_k_673_ = lean_ctor_get(v_t_671_, 1);
v_v_674_ = lean_ctor_get(v_t_671_, 2);
v_l_675_ = lean_ctor_get(v_t_671_, 3);
v_r_676_ = lean_ctor_get(v_t_671_, 4);
v___x_677_ = lean_unbox_uint64(v_k_673_);
v___x_678_ = lean_uint64_dec_lt(v_k_672_, v___x_677_);
if (v___x_678_ == 0)
{
uint64_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_unbox_uint64(v_k_673_);
v___x_680_ = lean_uint64_dec_eq(v_k_672_, v___x_679_);
if (v___x_680_ == 0)
{
v_t_671_ = v_r_676_;
goto _start;
}
else
{
lean_object* v___x_682_; 
lean_inc(v_v_674_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_v_674_);
return v___x_682_;
}
}
else
{
v_t_671_ = v_l_675_;
goto _start;
}
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_box(0);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_685_, lean_object* v_k_686_){
_start:
{
uint64_t v_k_boxed_687_; lean_object* v_res_688_; 
v_k_boxed_687_ = lean_unbox_uint64(v_k_686_);
lean_dec_ref(v_k_686_);
v_res_688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_685_, v_k_boxed_687_);
lean_dec(v_t_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_msgData_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_env_696_; uint8_t v___x_697_; lean_object* v_env_698_; lean_object* v___x_699_; lean_object* v_toCold_700_; lean_object* v_mctx_701_; lean_object* v_lctx_702_; lean_object* v_options_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_695_ = lean_st_ref_get(v___y_693_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_695_);
v___x_697_ = 0;
v_env_698_ = l_Lean_Environment_setRecordingDeps(v_env_696_, v___x_697_);
v___x_699_ = lean_st_ref_get(v___y_691_);
v_toCold_700_ = lean_ctor_get(v___y_692_, 0);
v_mctx_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_mctx_701_);
lean_dec(v___x_699_);
v_lctx_702_ = lean_ctor_get(v___y_690_, 2);
v_options_703_ = lean_ctor_get(v_toCold_700_, 2);
lean_inc_ref(v_options_703_);
lean_inc_ref(v_lctx_702_);
v___x_704_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_704_, 0, v_env_698_);
lean_ctor_set(v___x_704_, 1, v_mctx_701_);
lean_ctor_set(v___x_704_, 2, v_lctx_702_);
lean_ctor_set(v___x_704_, 3, v_options_703_);
v___x_705_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_msgData_689_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msgData_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_msg_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_ref_720_; lean_object* v___x_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
v_ref_720_ = lean_ctor_get(v___y_717_, 2);
v___x_721_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msg_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_inc(v_ref_720_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_ref_720_);
lean_ctor_set(v___x_726_, 1, v_a_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 1);
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_750_, uint8_t v_kind_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___y_763_; 
v___x_757_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_758_ = l_Lean_MessageData_ofName(v_name_750_);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
switch(v_kind_751_)
{
case 0:
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_763_ = v___x_770_;
goto v___jp_762_;
}
case 1:
{
lean_object* v___x_771_; 
v___x_771_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_763_ = v___x_771_;
goto v___jp_762_;
}
default: 
{
lean_object* v___x_772_; 
v___x_772_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_763_ = v___x_772_;
goto v___jp_762_;
}
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_inc_ref(v___y_763_);
v___x_764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_764_, 0, v___y_763_);
v___x_765_ = l_Lean_MessageData_ofFormat(v___x_764_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_761_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_768_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_773_, lean_object* v_kind_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v_kind_boxed_780_; lean_object* v_res_781_; 
v_kind_boxed_780_ = lean_unbox(v_kind_774_);
v_res_781_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_773_, v_kind_boxed_780_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_781_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t v_suppressElabErrors_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 1)
{
lean_object* v_pre_792_; 
v_pre_792_ = lean_ctor_get(v_x_791_, 0);
switch(lean_obj_tag(v_pre_792_))
{
case 1:
{
lean_object* v_pre_793_; 
v_pre_793_ = lean_ctor_get(v_pre_792_, 0);
switch(lean_obj_tag(v_pre_793_))
{
case 0:
{
lean_object* v_str_794_; lean_object* v_str_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_str_794_ = lean_ctor_get(v_x_791_, 1);
v_str_795_ = lean_ctor_get(v_pre_792_, 1);
v___x_796_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_797_ = lean_string_dec_eq(v_str_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_799_ = lean_string_dec_eq(v_str_795_, v___x_798_);
if (v___x_799_ == 0)
{
return v___x_799_;
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_801_ = lean_string_dec_eq(v_str_794_, v___x_800_);
if (v___x_801_ == 0)
{
return v___x_801_;
}
else
{
return v_suppressElabErrors_790_;
}
}
}
else
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_803_ = lean_string_dec_eq(v_str_794_, v___x_802_);
if (v___x_803_ == 0)
{
return v___x_803_;
}
else
{
return v_suppressElabErrors_790_;
}
}
}
case 1:
{
lean_object* v_pre_804_; 
v_pre_804_ = lean_ctor_get(v_pre_793_, 0);
if (lean_obj_tag(v_pre_804_) == 0)
{
lean_object* v_str_805_; lean_object* v_str_806_; lean_object* v_str_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_str_805_ = lean_ctor_get(v_x_791_, 1);
v_str_806_ = lean_ctor_get(v_pre_792_, 1);
v_str_807_ = lean_ctor_get(v_pre_793_, 1);
v___x_808_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_809_ = lean_string_dec_eq(v_str_807_, v___x_808_);
if (v___x_809_ == 0)
{
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_811_ = lean_string_dec_eq(v_str_806_, v___x_810_);
if (v___x_811_ == 0)
{
return v___x_811_;
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6));
v___x_813_ = lean_string_dec_eq(v_str_805_, v___x_812_);
if (v___x_813_ == 0)
{
return v___x_813_;
}
else
{
return v_suppressElabErrors_790_;
}
}
}
}
else
{
uint8_t v___x_814_; 
v___x_814_ = 0;
return v___x_814_;
}
}
default: 
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
case 0:
{
lean_object* v_str_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_str_816_ = lean_ctor_get(v_x_791_, 1);
v___x_817_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7));
v___x_818_ = lean_string_dec_eq(v_str_816_, v___x_817_);
if (v___x_818_ == 0)
{
return v___x_818_;
}
else
{
return v_suppressElabErrors_790_;
}
}
default: 
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
}
}
else
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_suppressElabErrors_boxed_823_; uint8_t v_res_824_; lean_object* v_r_825_; 
v_suppressElabErrors_boxed_823_ = lean_unbox(v_suppressElabErrors_821_);
v_res_824_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_boxed_823_, v_x_822_);
lean_dec(v_x_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_opts_826_, lean_object* v_opt_827_){
_start:
{
lean_object* v_name_828_; lean_object* v_defValue_829_; lean_object* v_map_830_; lean_object* v___x_831_; 
v_name_828_ = lean_ctor_get(v_opt_827_, 0);
v_defValue_829_ = lean_ctor_get(v_opt_827_, 1);
v_map_830_ = lean_ctor_get(v_opts_826_, 0);
v___x_831_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_830_, v_name_828_);
if (lean_obj_tag(v___x_831_) == 0)
{
uint8_t v___x_832_; 
v___x_832_ = lean_unbox(v_defValue_829_);
return v___x_832_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_831_, 1);
if (lean_obj_tag(v_val_833_) == 1)
{
uint8_t v_v_834_; 
v_v_834_ = lean_ctor_get_uint8(v_val_833_, 0);
lean_dec_ref_known(v_val_833_, 0);
return v_v_834_;
}
else
{
uint8_t v___x_835_; 
lean_dec(v_val_833_);
v___x_835_ = lean_unbox(v_defValue_829_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_opts_836_, lean_object* v_opt_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_opts_836_, v_opt_837_);
lean_dec_ref(v_opt_837_);
lean_dec_ref(v_opts_836_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_ref_841_, lean_object* v_msgData_842_, uint8_t v_severity_843_, uint8_t v_isSilent_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___y_851_; uint8_t v___y_852_; uint8_t v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v_toCold_858_; lean_object* v___y_859_; lean_object* v___y_888_; lean_object* v___y_889_; uint8_t v___y_890_; uint8_t v___y_891_; lean_object* v___y_892_; uint8_t v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_915_; lean_object* v___y_916_; uint8_t v___y_917_; uint8_t v___y_918_; uint8_t v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; uint8_t v___y_925_; uint8_t v___y_926_; uint8_t v___x_936_; uint8_t v___y_938_; uint8_t v___x_944_; 
v___x_936_ = 2;
v___x_944_ = l_Lean_instBEqMessageSeverity_beq(v_severity_843_, v___x_936_);
if (v___x_944_ == 0)
{
v___y_938_ = v___x_944_;
goto v___jp_937_;
}
else
{
uint8_t v___x_945_; 
lean_inc_ref(v_msgData_842_);
v___x_945_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_842_);
if (v___x_945_ == 0)
{
v___y_938_ = v___x_945_;
goto v___jp_937_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref(v_msgData_842_);
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
v___jp_850_:
{
lean_object* v_currNamespace_860_; lean_object* v_openDecls_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_env_866_; lean_object* v_nextMacroScope_867_; lean_object* v_ngen_868_; lean_object* v_auxDeclNGen_869_; lean_object* v_traceState_870_; lean_object* v_cache_871_; lean_object* v_recordedDeps_872_; lean_object* v_messages_873_; lean_object* v_infoState_874_; lean_object* v_snapshotTasks_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_886_; 
v_currNamespace_860_ = lean_ctor_get(v_toCold_858_, 4);
v_openDecls_861_ = lean_ctor_get(v_toCold_858_, 5);
lean_inc(v_openDecls_861_);
lean_inc(v_currNamespace_860_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_currNamespace_860_);
lean_ctor_set(v___x_862_, 1, v_openDecls_861_);
v___x_863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc_ref(v___y_851_);
v___x_864_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_864_, 0, v___y_851_);
lean_ctor_set(v___x_864_, 1, v___y_855_);
lean_ctor_set(v___x_864_, 2, v___y_854_);
lean_ctor_set(v___x_864_, 3, v___y_856_);
lean_ctor_set(v___x_864_, 4, v___x_863_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*5, v___y_852_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*5 + 1, v___y_853_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*5 + 2, v_isSilent_844_);
v___x_865_ = lean_st_ref_take(v___y_859_);
v_env_866_ = lean_ctor_get(v___x_865_, 0);
v_nextMacroScope_867_ = lean_ctor_get(v___x_865_, 1);
v_ngen_868_ = lean_ctor_get(v___x_865_, 2);
v_auxDeclNGen_869_ = lean_ctor_get(v___x_865_, 3);
v_traceState_870_ = lean_ctor_get(v___x_865_, 4);
v_cache_871_ = lean_ctor_get(v___x_865_, 5);
v_recordedDeps_872_ = lean_ctor_get(v___x_865_, 6);
v_messages_873_ = lean_ctor_get(v___x_865_, 7);
v_infoState_874_ = lean_ctor_get(v___x_865_, 8);
v_snapshotTasks_875_ = lean_ctor_get(v___x_865_, 9);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_886_ == 0)
{
v___x_877_ = v___x_865_;
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snapshotTasks_875_);
lean_inc(v_infoState_874_);
lean_inc(v_messages_873_);
lean_inc(v_recordedDeps_872_);
lean_inc(v_cache_871_);
lean_inc(v_traceState_870_);
lean_inc(v_auxDeclNGen_869_);
lean_inc(v_ngen_868_);
lean_inc(v_nextMacroScope_867_);
lean_inc(v_env_866_);
lean_dec(v___x_865_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = lean_box(0);
v___x_880_ = l_Lean_MessageLog_add(v___x_864_, v_messages_873_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 7, v___x_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_env_866_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_nextMacroScope_867_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_ngen_868_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_auxDeclNGen_869_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_traceState_870_);
lean_ctor_set(v_reuseFailAlloc_885_, 5, v_cache_871_);
lean_ctor_set(v_reuseFailAlloc_885_, 6, v_recordedDeps_872_);
lean_ctor_set(v_reuseFailAlloc_885_, 7, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_885_, 8, v_infoState_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 9, v_snapshotTasks_875_);
v___x_882_ = v_reuseFailAlloc_885_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_st_ref_put(v___y_859_, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_879_);
return v___x_884_;
}
}
}
v___jp_887_:
{
lean_object* v_fileName_896_; lean_object* v_fileMap_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_913_; 
v_fileName_896_ = lean_ctor_get(v___y_892_, 0);
v_fileMap_897_ = lean_ctor_get(v___y_892_, 1);
v___x_898_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_842_);
v___x_899_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v___x_898_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_913_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_913_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_913_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_inc_ref_n(v_fileMap_897_, 2);
v___x_904_ = l_Lean_FileMap_toPosition(v_fileMap_897_, v___y_894_);
lean_dec(v___y_894_);
v___x_905_ = l_Lean_FileMap_toPosition(v_fileMap_897_, v___y_895_);
lean_dec(v___y_895_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
if (v___y_893_ == 0)
{
lean_del_object(v___x_902_);
lean_dec_ref(v___y_888_);
v___y_851_ = v_fileName_896_;
v___y_852_ = v___y_890_;
v___y_853_ = v___y_891_;
v___y_854_ = v___x_906_;
v___y_855_ = v___x_904_;
v___y_856_ = v___x_907_;
v___y_857_ = v_a_900_;
v_toCold_858_ = v___y_889_;
v___y_859_ = v___y_848_;
goto v___jp_850_;
}
else
{
uint8_t v___x_908_; 
lean_inc(v_a_900_);
v___x_908_ = l_Lean_MessageData_hasTag(v___y_888_, v_a_900_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec_ref_known(v___x_906_, 1);
lean_dec_ref(v___x_904_);
lean_dec(v_a_900_);
v___x_909_ = lean_box(0);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_909_);
v___x_911_ = v___x_902_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_del_object(v___x_902_);
v___y_851_ = v_fileName_896_;
v___y_852_ = v___y_890_;
v___y_853_ = v___y_891_;
v___y_854_ = v___x_906_;
v___y_855_ = v___x_904_;
v___y_856_ = v___x_907_;
v___y_857_ = v_a_900_;
v_toCold_858_ = v___y_889_;
v___y_859_ = v___y_848_;
goto v___jp_850_;
}
}
}
}
v___jp_914_:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Syntax_getTailPos_x3f(v___y_920_, v___y_918_);
lean_dec(v___y_920_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_inc(v___y_921_);
v___y_888_ = v___y_915_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_918_;
v___y_891_ = v___y_919_;
v___y_892_ = v___y_916_;
v___y_893_ = v___y_917_;
v___y_894_ = v___y_921_;
v___y_895_ = v___y_921_;
goto v___jp_887_;
}
else
{
lean_object* v_val_923_; 
v_val_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v___x_922_, 1);
v___y_888_ = v___y_915_;
v___y_889_ = v___y_916_;
v___y_890_ = v___y_918_;
v___y_891_ = v___y_919_;
v___y_892_ = v___y_916_;
v___y_893_ = v___y_917_;
v___y_894_ = v___y_921_;
v___y_895_ = v_val_923_;
goto v___jp_887_;
}
}
v___jp_924_:
{
lean_object* v_toCold_927_; lean_object* v_ref_928_; uint8_t v_suppressElabErrors_929_; lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v_ref_932_; lean_object* v___x_933_; 
v_toCold_927_ = lean_ctor_get(v___y_847_, 0);
v_ref_928_ = lean_ctor_get(v___y_847_, 2);
v_suppressElabErrors_929_ = lean_ctor_get_uint8(v___y_847_, sizeof(void*)*3 + 2);
v___x_930_ = lean_box(v_suppressElabErrors_929_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_931_, 0, v___x_930_);
v_ref_932_ = l_Lean_replaceRef(v_ref_841_, v_ref_928_);
v___x_933_ = l_Lean_Syntax_getPos_x3f(v_ref_932_, v___y_925_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___y_915_ = v___f_931_;
v___y_916_ = v_toCold_927_;
v___y_917_ = v_suppressElabErrors_929_;
v___y_918_ = v___y_925_;
v___y_919_ = v___y_926_;
v___y_920_ = v_ref_932_;
v___y_921_ = v___x_934_;
goto v___jp_914_;
}
else
{
lean_object* v_val_935_; 
v_val_935_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v___x_933_, 1);
v___y_915_ = v___f_931_;
v___y_916_ = v_toCold_927_;
v___y_917_ = v_suppressElabErrors_929_;
v___y_918_ = v___y_925_;
v___y_919_ = v___y_926_;
v___y_920_ = v_ref_932_;
v___y_921_ = v_val_935_;
goto v___jp_914_;
}
}
v___jp_937_:
{
uint8_t v___x_939_; uint8_t v___x_940_; 
v___x_939_ = 1;
v___x_940_ = l_Lean_instBEqMessageSeverity_beq(v_severity_843_, v___x_939_);
if (v___x_940_ == 0)
{
v___y_925_ = v___y_938_;
v___y_926_ = v_severity_843_;
goto v___jp_924_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_847_);
v___x_942_ = l_Lean_warningAsError;
v___x_943_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v___x_941_, v___x_942_);
lean_dec_ref(v___x_941_);
if (v___x_943_ == 0)
{
v___y_925_ = v___y_938_;
v___y_926_ = v_severity_843_;
goto v___jp_924_;
}
else
{
v___y_925_ = v___y_938_;
v___y_926_ = v___x_936_;
goto v___jp_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_ref_948_, lean_object* v_msgData_949_, lean_object* v_severity_950_, lean_object* v_isSilent_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
uint8_t v_severity_boxed_957_; uint8_t v_isSilent_boxed_958_; lean_object* v_res_959_; 
v_severity_boxed_957_ = lean_unbox(v_severity_950_);
v_isSilent_boxed_958_ = lean_unbox(v_isSilent_951_);
v_res_959_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_948_, v_msgData_949_, v_severity_boxed_957_, v_isSilent_boxed_958_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v_ref_948_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_msgData_960_, uint8_t v_severity_961_, uint8_t v_isSilent_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_ref_968_; lean_object* v___x_969_; 
v_ref_968_ = lean_ctor_get(v___y_965_, 2);
v___x_969_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_968_, v_msgData_960_, v_severity_961_, v_isSilent_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_msgData_970_, lean_object* v_severity_971_, lean_object* v_isSilent_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v_severity_boxed_978_; uint8_t v_isSilent_boxed_979_; lean_object* v_res_980_; 
v_severity_boxed_978_ = lean_unbox(v_severity_971_);
v_isSilent_boxed_979_ = lean_unbox(v_isSilent_972_);
v_res_980_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_970_, v_severity_boxed_978_, v_isSilent_boxed_979_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(lean_object* v_msgData_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = 1;
v___x_988_ = 0;
v___x_989_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_981_, v___x_987_, v___x_988_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3___boxed(lean_object* v_msgData_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v_msgData_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__7_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t v_builtin_1009_, lean_object* v_decl_1010_, uint8_t v___x_1011_, lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v_stx_1014_, uint8_t v_kind_1015_, lean_object* v_name_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1014_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1125_) == 0)
{
uint8_t v___x_1126_; uint8_t v___x_1127_; 
lean_dec_ref_known(v___x_1125_, 1);
v___x_1126_ = 0;
v___x_1127_ = l_Lean_instBEqAttributeKind_beq(v_kind_1015_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
lean_dec(v_decl_1010_);
v___x_1128_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_1016_, v_kind_1015_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1128_;
}
else
{
lean_dec(v_name_1016_);
goto v___jp_1087_;
}
}
else
{
lean_dec(v_name_1016_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
lean_dec(v_decl_1010_);
return v___x_1125_;
}
v___jp_1022_:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_st_ref_get(v___y_1029_);
if (v_builtin_1009_ == 0)
{
lean_object* v_env_1031_; uint64_t v_javascriptHash_1032_; lean_object* v___x_1033_; lean_object* v_toEnvExtension_1034_; lean_object* v_addEntryFn_1035_; lean_object* v_asyncMode_1036_; uint8_t v_logWrites_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; 
lean_dec(v___y_1025_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
v_env_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_env_1031_);
lean_dec(v___x_1030_);
v_javascriptHash_1032_ = lean_ctor_get_uint64(v___y_1024_, sizeof(void*)*1);
lean_dec_ref(v___y_1024_);
v___x_1033_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1034_ = lean_ctor_get(v___x_1033_, 0);
v_addEntryFn_1035_ = lean_ctor_get(v___x_1033_, 3);
v_asyncMode_1036_ = lean_ctor_get(v_toEnvExtension_1034_, 2);
v_logWrites_1037_ = lean_ctor_get_uint8(v_toEnvExtension_1034_, sizeof(void*)*6);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_decl_1010_);
lean_ctor_set(v___x_1038_, 1, v___y_1023_);
v___x_1039_ = lean_box_uint64(v_javascriptHash_1032_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_1038_);
lean_inc(v_addEntryFn_1035_);
v___f_1041_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1041_, 0, v_addEntryFn_1035_);
lean_closure_set(v___f_1041_, 1, v___x_1040_);
v___x_1042_ = lean_box(0);
if (v_logWrites_1037_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_inc_ref(v_toEnvExtension_1034_);
v___x_1043_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1034_, v_env_1031_, v___f_1041_, v_asyncMode_1036_, v___x_1042_, v___x_1011_);
v___x_1044_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v___x_1043_, v___y_1027_, v___y_1029_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_inc_ref_n(v_toEnvExtension_1034_, 2);
v___x_1045_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1034_, v_env_1031_);
lean_dec_ref(v_env_1031_);
v___x_1046_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1034_, v___x_1045_, v___f_1041_, v_asyncMode_1036_, v___x_1042_, v___x_1011_);
v___x_1047_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v___x_1046_, v___y_1027_, v___y_1029_);
return v___x_1047_;
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v___x_1030_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_inc(v___y_1025_);
lean_inc_n(v_decl_1010_, 2);
v___x_1048_ = l_Lean_mkConst(v_decl_1010_, v___y_1025_);
v___x_1049_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1050_ = l_Lean_Name_mkStr3(v___x_1012_, v___x_1013_, v___x_1049_);
v___x_1051_ = l_Lean_mkConst(v___x_1050_, v___y_1025_);
v___x_1052_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_1010_);
v___x_1053_ = l_Lean_mkAppB(v___x_1051_, v___x_1052_, v___x_1048_);
v___x_1054_ = l_Lean_declareBuiltin(v_decl_1010_, v___x_1053_, v___y_1028_, v___y_1029_);
return v___x_1054_;
}
}
v___jp_1055_:
{
lean_object* v___x_1064_; lean_object* v_toEnvExtension_1065_; lean_object* v_asyncMode_1066_; uint64_t v_javascriptHash_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1064_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1065_ = lean_ctor_get(v___x_1064_, 0);
v_asyncMode_1066_ = lean_ctor_get(v_toEnvExtension_1065_, 2);
v_javascriptHash_1067_ = lean_ctor_get_uint64(v___y_1058_, sizeof(void*)*1);
v___x_1068_ = lean_box(1);
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1068_, v___x_1064_, v___y_1056_, v_asyncMode_1066_, v___x_1069_);
v___x_1071_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1070_, v_javascriptHash_1067_);
lean_dec(v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 1)
{
lean_object* v_val_1072_; lean_object* v_fst_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1085_; 
v_val_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_fst_1073_ = lean_ctor_get(v_val_1072_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_val_1072_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_val_1072_, 1);
lean_dec(v_unused_1086_);
v___x_1075_ = v_val_1072_;
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_fst_1073_);
lean_dec(v_val_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1078_ = l_Lean_MessageData_ofConstName(v_fst_1073_, v___x_1011_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 7);
lean_ctor_set(v___x_1075_, 1, v___x_1078_);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v___x_1082_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_dec_ref_known(v___x_1083_, 1);
v___y_1023_ = v___y_1057_;
v___y_1024_ = v___y_1058_;
v___y_1025_ = v___y_1059_;
v___y_1026_ = v___y_1060_;
v___y_1027_ = v___y_1061_;
v___y_1028_ = v___y_1062_;
v___y_1029_ = v___y_1063_;
goto v___jp_1022_;
}
else
{
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
lean_dec(v_decl_1010_);
return v___x_1083_;
}
}
}
}
else
{
lean_dec(v___x_1071_);
v___y_1023_ = v___y_1057_;
v___y_1024_ = v___y_1058_;
v___y_1025_ = v___y_1059_;
v___y_1026_ = v___y_1060_;
v___y_1027_ = v___y_1061_;
v___y_1028_ = v___y_1062_;
v___y_1029_ = v___y_1063_;
goto v___jp_1022_;
}
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1089_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
lean_inc_ref(v___x_1013_);
lean_inc_ref(v___x_1012_);
v___x_1090_ = l_Lean_Name_mkStr4(v___x_1012_, v___x_1013_, v___x_1088_, v___x_1089_);
v___x_1091_ = lean_box(0);
lean_inc(v_decl_1010_);
v___x_1092_ = l_Lean_Expr_const___override(v_decl_1010_, v___x_1091_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_mk_empty_array_with_capacity(v___x_1093_);
v___x_1095_ = lean_array_push(v___x_1094_, v___x_1092_);
v___x_1096_ = l_Lean_Meta_mkAppM(v___x_1090_, v___x_1095_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_n(v_a_1097_, 2);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_1097_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = lean_st_ref_get(v___y_1020_);
if (v_builtin_1009_ == 0)
{
lean_object* v_env_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint64_t v_javascriptHash_1104_; lean_object* v___x_1105_; 
v_env_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_env_1101_);
lean_dec(v___x_1100_);
v___x_1102_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1103_ = lean_st_ref_get(v___x_1102_);
v_javascriptHash_1104_ = lean_ctor_get_uint64(v_a_1099_, sizeof(void*)*1);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1103_, v_javascriptHash_1104_);
lean_dec(v___x_1103_);
if (lean_obj_tag(v___x_1105_) == 1)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref_known(v___x_1105_, 1);
v___x_1106_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1107_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v___x_1106_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
v___y_1056_ = v_env_1101_;
v___y_1057_ = v_a_1097_;
v___y_1058_ = v_a_1099_;
v___y_1059_ = v___x_1091_;
v___y_1060_ = v___y_1017_;
v___y_1061_ = v___y_1018_;
v___y_1062_ = v___y_1019_;
v___y_1063_ = v___y_1020_;
goto v___jp_1055_;
}
else
{
lean_dec_ref(v_env_1101_);
lean_dec(v_a_1099_);
lean_dec(v_a_1097_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
lean_dec(v_decl_1010_);
return v___x_1107_;
}
}
else
{
lean_dec(v___x_1105_);
v___y_1056_ = v_env_1101_;
v___y_1057_ = v_a_1097_;
v___y_1058_ = v_a_1099_;
v___y_1059_ = v___x_1091_;
v___y_1060_ = v___y_1017_;
v___y_1061_ = v___y_1018_;
v___y_1062_ = v___y_1019_;
v___y_1063_ = v___y_1020_;
goto v___jp_1055_;
}
}
else
{
lean_object* v_env_1108_; 
v_env_1108_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_env_1108_);
lean_dec(v___x_1100_);
v___y_1056_ = v_env_1108_;
v___y_1057_ = v_a_1097_;
v___y_1058_ = v_a_1099_;
v___y_1059_ = v___x_1091_;
v___y_1060_ = v___y_1017_;
v___y_1061_ = v___y_1018_;
v___y_1062_ = v___y_1019_;
v___y_1063_ = v___y_1020_;
goto v___jp_1055_;
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_a_1097_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
lean_dec(v_decl_1010_);
v_a_1109_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1098_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1098_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v___x_1013_);
lean_dec_ref(v___x_1012_);
lean_dec(v_decl_1010_);
v_a_1117_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1096_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1096_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_builtin_1129_, lean_object* v_decl_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v_stx_1134_, lean_object* v_kind_1135_, lean_object* v_name_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
uint8_t v_builtin_boxed_1142_; uint8_t v___x_11569__boxed_1143_; uint8_t v_kind_boxed_1144_; lean_object* v_res_1145_; 
v_builtin_boxed_1142_ = lean_unbox(v_builtin_1129_);
v___x_11569__boxed_1143_ = lean_unbox(v___x_1131_);
v_kind_boxed_1144_ = lean_unbox(v_kind_1135_);
v_res_1145_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_boxed_1142_, v_decl_1130_, v___x_11569__boxed_1143_, v___x_1132_, v___x_1133_, v_stx_1134_, v_kind_boxed_1144_, v_name_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object* v___y_1146_, uint8_t v_isExporting_1147_, lean_object* v___x_1148_, lean_object* v___y_1149_, lean_object* v___x_1150_, lean_object* v_a_x3f_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v_env_1154_; lean_object* v_nextMacroScope_1155_; lean_object* v_ngen_1156_; lean_object* v_auxDeclNGen_1157_; lean_object* v_traceState_1158_; lean_object* v_recordedDeps_1159_; lean_object* v_messages_1160_; lean_object* v_infoState_1161_; lean_object* v_snapshotTasks_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1187_; 
v___x_1153_ = lean_st_ref_take(v___y_1146_);
v_env_1154_ = lean_ctor_get(v___x_1153_, 0);
v_nextMacroScope_1155_ = lean_ctor_get(v___x_1153_, 1);
v_ngen_1156_ = lean_ctor_get(v___x_1153_, 2);
v_auxDeclNGen_1157_ = lean_ctor_get(v___x_1153_, 3);
v_traceState_1158_ = lean_ctor_get(v___x_1153_, 4);
v_recordedDeps_1159_ = lean_ctor_get(v___x_1153_, 6);
v_messages_1160_ = lean_ctor_get(v___x_1153_, 7);
v_infoState_1161_ = lean_ctor_get(v___x_1153_, 8);
v_snapshotTasks_1162_ = lean_ctor_get(v___x_1153_, 9);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v___x_1153_, 5);
lean_dec(v_unused_1188_);
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1187_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snapshotTasks_1162_);
lean_inc(v_infoState_1161_);
lean_inc(v_messages_1160_);
lean_inc(v_recordedDeps_1159_);
lean_inc(v_traceState_1158_);
lean_inc(v_auxDeclNGen_1157_);
lean_inc(v_ngen_1156_);
lean_inc(v_nextMacroScope_1155_);
lean_inc(v_env_1154_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1187_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = l_Lean_Environment_setExporting(v_env_1154_, v_isExporting_1147_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 5, v___x_1148_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_nextMacroScope_1155_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_ngen_1156_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_auxDeclNGen_1157_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_traceState_1158_);
lean_ctor_set(v_reuseFailAlloc_1186_, 5, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1186_, 6, v_recordedDeps_1159_);
lean_ctor_set(v_reuseFailAlloc_1186_, 7, v_messages_1160_);
lean_ctor_set(v_reuseFailAlloc_1186_, 8, v_infoState_1161_);
lean_ctor_set(v_reuseFailAlloc_1186_, 9, v_snapshotTasks_1162_);
v___x_1168_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_mctx_1171_; lean_object* v_zetaDeltaFVarIds_1172_; lean_object* v_postponed_1173_; lean_object* v_diag_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1184_; 
v___x_1169_ = lean_st_ref_put(v___y_1146_, v___x_1168_);
v___x_1170_ = lean_st_ref_take(v___y_1149_);
v_mctx_1171_ = lean_ctor_get(v___x_1170_, 0);
v_zetaDeltaFVarIds_1172_ = lean_ctor_get(v___x_1170_, 2);
v_postponed_1173_ = lean_ctor_get(v___x_1170_, 3);
v_diag_1174_ = lean_ctor_get(v___x_1170_, 4);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v___x_1170_, 1);
lean_dec(v_unused_1185_);
v___x_1176_ = v___x_1170_;
v_isShared_1177_ = v_isSharedCheck_1184_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_diag_1174_);
lean_inc(v_postponed_1173_);
lean_inc(v_zetaDeltaFVarIds_1172_);
lean_inc(v_mctx_1171_);
lean_dec(v___x_1170_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1184_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_box(0);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1150_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_mctx_1171_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_zetaDeltaFVarIds_1172_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_postponed_1173_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_diag_1174_);
v___x_1180_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_st_ref_put(v___y_1149_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1178_);
return v___x_1182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object* v___y_1189_, lean_object* v_isExporting_1190_, lean_object* v___x_1191_, lean_object* v___y_1192_, lean_object* v___x_1193_, lean_object* v_a_x3f_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_isExporting_boxed_1196_; lean_object* v_res_1197_; 
v_isExporting_boxed_1196_ = lean_unbox(v_isExporting_1190_);
v_res_1197_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1189_, v_isExporting_boxed_1196_, v___x_1191_, v___y_1192_, v___x_1193_, v_a_x3f_1194_);
lean_dec(v_a_x3f_1194_);
lean_dec(v___y_1192_);
lean_dec(v___y_1189_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object* v_x_1198_, uint8_t v_isExporting_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v_env_1206_; lean_object* v___x_1207_; uint8_t v_isModule_1208_; 
v___x_1205_ = lean_st_ref_get(v___y_1203_);
v_env_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_ref(v_env_1206_);
lean_dec(v___x_1205_);
v___x_1207_ = l_Lean_Environment_header(v_env_1206_);
v_isModule_1208_ = lean_ctor_get_uint8(v___x_1207_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1207_);
if (v_isModule_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v_env_1206_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v___x_1209_ = lean_apply_5(v_x_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1209_;
}
else
{
uint8_t v_isExporting_1210_; 
v_isExporting_1210_ = lean_ctor_get_uint8(v_env_1206_, sizeof(void*)*13);
lean_dec_ref(v_env_1206_);
if (v_isExporting_1199_ == 0)
{
if (v_isExporting_1210_ == 0)
{
lean_object* v___x_1277_; 
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v___x_1277_ = lean_apply_5(v_x_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1277_;
}
else
{
goto v___jp_1211_;
}
}
else
{
if (v_isExporting_1210_ == 0)
{
goto v___jp_1211_;
}
else
{
lean_object* v___x_1278_; 
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v___x_1278_ = lean_apply_5(v_x_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1278_;
}
}
v___jp_1211_:
{
lean_object* v___x_1212_; lean_object* v_env_1213_; lean_object* v_nextMacroScope_1214_; lean_object* v_ngen_1215_; lean_object* v_auxDeclNGen_1216_; lean_object* v_traceState_1217_; lean_object* v_recordedDeps_1218_; lean_object* v_messages_1219_; lean_object* v_infoState_1220_; lean_object* v_snapshotTasks_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1275_; 
v___x_1212_ = lean_st_ref_take(v___y_1203_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
v_nextMacroScope_1214_ = lean_ctor_get(v___x_1212_, 1);
v_ngen_1215_ = lean_ctor_get(v___x_1212_, 2);
v_auxDeclNGen_1216_ = lean_ctor_get(v___x_1212_, 3);
v_traceState_1217_ = lean_ctor_get(v___x_1212_, 4);
v_recordedDeps_1218_ = lean_ctor_get(v___x_1212_, 6);
v_messages_1219_ = lean_ctor_get(v___x_1212_, 7);
v_infoState_1220_ = lean_ctor_get(v___x_1212_, 8);
v_snapshotTasks_1221_ = lean_ctor_get(v___x_1212_, 9);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1212_, 5);
lean_dec(v_unused_1276_);
v___x_1223_ = v___x_1212_;
v_isShared_1224_ = v_isSharedCheck_1275_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snapshotTasks_1221_);
lean_inc(v_infoState_1220_);
lean_inc(v_messages_1219_);
lean_inc(v_recordedDeps_1218_);
lean_inc(v_traceState_1217_);
lean_inc(v_auxDeclNGen_1216_);
lean_inc(v_ngen_1215_);
lean_inc(v_nextMacroScope_1214_);
lean_inc(v_env_1213_);
lean_dec(v___x_1212_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1275_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1225_ = l_Lean_Environment_setExporting(v_env_1213_, v_isExporting_1199_);
v___x_1226_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 5, v___x_1226_);
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1228_ = v___x_1223_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_nextMacroScope_1214_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_ngen_1215_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_auxDeclNGen_1216_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_traceState_1217_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1274_, 6, v_recordedDeps_1218_);
lean_ctor_set(v_reuseFailAlloc_1274_, 7, v_messages_1219_);
lean_ctor_set(v_reuseFailAlloc_1274_, 8, v_infoState_1220_);
lean_ctor_set(v_reuseFailAlloc_1274_, 9, v_snapshotTasks_1221_);
v___x_1228_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_mctx_1231_; lean_object* v_zetaDeltaFVarIds_1232_; lean_object* v_postponed_1233_; lean_object* v_diag_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1272_; 
v___x_1229_ = lean_st_ref_put(v___y_1203_, v___x_1228_);
v___x_1230_ = lean_st_ref_take(v___y_1201_);
v_mctx_1231_ = lean_ctor_get(v___x_1230_, 0);
v_zetaDeltaFVarIds_1232_ = lean_ctor_get(v___x_1230_, 2);
v_postponed_1233_ = lean_ctor_get(v___x_1230_, 3);
v_diag_1234_ = lean_ctor_get(v___x_1230_, 4);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1230_, 1);
lean_dec(v_unused_1273_);
v___x_1236_ = v___x_1230_;
v_isShared_1237_ = v_isSharedCheck_1272_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_diag_1234_);
lean_inc(v_postponed_1233_);
lean_inc(v_zetaDeltaFVarIds_1232_);
lean_inc(v_mctx_1231_);
lean_dec(v___x_1230_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1272_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___x_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_mctx_1231_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_zetaDeltaFVarIds_1232_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_postponed_1233_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_diag_1234_);
v___x_1240_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; lean_object* v_r_1242_; 
v___x_1241_ = lean_st_ref_put(v___y_1201_, v___x_1240_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v_r_1242_ = lean_apply_5(v_x_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
if (lean_obj_tag(v_r_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1259_; 
v_a_1243_ = lean_ctor_get(v_r_1242_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_r_1242_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1245_ = v_r_1242_;
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v_r_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
lean_inc(v_a_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 1);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v___x_1249_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1203_, v_isExporting_1210_, v___x_1226_, v___y_1201_, v___x_1238_, v___x_1248_);
lean_dec_ref(v___x_1248_);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1257_);
v___x_1251_ = v___x_1249_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v___x_1249_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_a_1243_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1243_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1260_ = lean_ctor_get(v_r_1242_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v_r_1242_, 1);
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1203_, v_isExporting_1210_, v___x_1226_, v___y_1201_, v___x_1238_, v___x_1261_);
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
lean_ctor_set_tag(v___x_1264_, 1);
lean_ctor_set(v___x_1264_, 0, v_a_1260_);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1260_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object* v_x_1279_, lean_object* v_isExporting_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v_isExporting_boxed_1286_; lean_object* v_res_1287_; 
v_isExporting_boxed_1286_ = lean_unbox(v_isExporting_1280_);
v_res_1287_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1279_, v_isExporting_boxed_1286_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(lean_object* v_x_1288_, uint8_t v_when_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
if (v_when_1289_ == 0)
{
lean_object* v___x_1295_; 
lean_inc(v___y_1293_);
lean_inc_ref(v___y_1292_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
v___x_1295_ = lean_apply_5(v_x_1288_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, lean_box(0));
return v___x_1295_;
}
else
{
uint8_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = 0;
v___x_1297_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1288_, v___x_1296_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_x_1298_, lean_object* v_when_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_when_boxed_1305_; lean_object* v_res_1306_; 
v_when_boxed_1305_ = lean_unbox(v_when_1299_);
v_res_1306_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1298_, v_when_boxed_1305_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1306_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_box(1);
v___x_1310_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1311_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___x_1309_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1316_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_ctor_set(v___x_1318_, 2, v___x_1317_);
lean_ctor_set(v___x_1318_, 3, v___x_1317_);
lean_ctor_set(v___x_1318_, 4, v___x_1316_);
lean_ctor_set(v___x_1318_, 5, v___x_1316_);
lean_ctor_set(v___x_1318_, 6, v___x_1316_);
lean_ctor_set(v___x_1318_, 7, v___x_1316_);
lean_ctor_set(v___x_1318_, 8, v___x_1316_);
lean_ctor_set(v___x_1318_, 9, v___x_1316_);
lean_ctor_set(v___x_1318_, 10, v___x_1316_);
lean_ctor_set(v___x_1318_, 11, v___x_1315_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1320_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
lean_ctor_set(v___x_1320_, 2, v___x_1319_);
lean_ctor_set(v___x_1320_, 3, v___x_1319_);
lean_ctor_set(v___x_1320_, 4, v___x_1319_);
lean_ctor_set(v___x_1320_, 5, v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
lean_ctor_set(v___x_1322_, 2, v___x_1321_);
lean_ctor_set(v___x_1322_, 3, v___x_1321_);
lean_ctor_set(v___x_1322_, 4, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t v_builtin_1323_, uint8_t v___x_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v_name_1327_, lean_object* v___x_1328_, lean_object* v_decl_1329_, lean_object* v_stx_1330_, uint8_t v_kind_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___f_1338_; uint8_t v___x_1339_; uint8_t v___x_1340_; uint8_t v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; uint64_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1335_ = lean_box(v_builtin_1323_);
v___x_1336_ = lean_box(v___x_1324_);
v___x_1337_ = lean_box(v_kind_1331_);
v___f_1338_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 13, 8);
lean_closure_set(v___f_1338_, 0, v___x_1335_);
lean_closure_set(v___f_1338_, 1, v_decl_1329_);
lean_closure_set(v___f_1338_, 2, v___x_1336_);
lean_closure_set(v___f_1338_, 3, v___x_1325_);
lean_closure_set(v___f_1338_, 4, v___x_1326_);
lean_closure_set(v___f_1338_, 5, v_stx_1330_);
lean_closure_set(v___f_1338_, 6, v___x_1337_);
lean_closure_set(v___f_1338_, 7, v_name_1327_);
v___x_1339_ = 0;
v___x_1340_ = 1;
v___x_1341_ = 0;
v___x_1342_ = 2;
v___x_1343_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1343_, 0, v___x_1339_);
lean_ctor_set_uint8(v___x_1343_, 1, v___x_1339_);
lean_ctor_set_uint8(v___x_1343_, 2, v___x_1339_);
lean_ctor_set_uint8(v___x_1343_, 3, v___x_1339_);
lean_ctor_set_uint8(v___x_1343_, 4, v___x_1339_);
lean_ctor_set_uint8(v___x_1343_, 5, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 6, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 7, v___x_1339_);
lean_ctor_set_uint8(v___x_1343_, 8, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 9, v___x_1340_);
lean_ctor_set_uint8(v___x_1343_, 10, v___x_1341_);
lean_ctor_set_uint8(v___x_1343_, 11, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 12, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 13, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 14, v___x_1342_);
lean_ctor_set_uint8(v___x_1343_, 15, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 16, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 17, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 18, v___x_1324_);
lean_ctor_set_uint8(v___x_1343_, 19, v___x_1339_);
v___x_1344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1343_);
v___x_1345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set_uint64(v___x_1345_, sizeof(void*)*1, v___x_1344_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1348_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1350_ = lean_box(0);
lean_inc(v___x_1328_);
v___x_1351_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1351_, 0, v___x_1345_);
lean_ctor_set(v___x_1351_, 1, v___x_1328_);
lean_ctor_set(v___x_1351_, 2, v___x_1348_);
lean_ctor_set(v___x_1351_, 3, v___x_1349_);
lean_ctor_set(v___x_1351_, 4, v___x_1350_);
lean_ctor_set(v___x_1351_, 5, v___x_1346_);
lean_ctor_set(v___x_1351_, 6, v___x_1350_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7, v___x_1339_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7 + 1, v___x_1339_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7 + 2, v___x_1339_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*7 + 3, v___x_1324_);
v___x_1352_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1353_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1354_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1352_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
lean_ctor_set(v___x_1355_, 2, v___x_1328_);
lean_ctor_set(v___x_1355_, 3, v___x_1347_);
lean_ctor_set(v___x_1355_, 4, v___x_1354_);
v___x_1356_ = lean_st_mk_ref(v___x_1355_);
v___x_1357_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v___f_1338_, v___x_1324_, v___x_1351_, v___x_1356_, v___y_1332_, v___y_1333_);
lean_dec_ref_known(v___x_1351_, 7);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_st_ref_get(v___x_1356_);
lean_dec(v___x_1356_);
lean_dec(v___x_1362_);
if (v_isShared_1361_ == 0)
{
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1358_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_dec(v___x_1356_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_builtin_1367_, lean_object* v___x_1368_, lean_object* v___x_1369_, lean_object* v___x_1370_, lean_object* v_name_1371_, lean_object* v___x_1372_, lean_object* v_decl_1373_, lean_object* v_stx_1374_, lean_object* v_kind_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v_builtin_boxed_1379_; uint8_t v___x_12114__boxed_1380_; uint8_t v_kind_boxed_1381_; lean_object* v_res_1382_; 
v_builtin_boxed_1379_ = lean_unbox(v_builtin_1367_);
v___x_12114__boxed_1380_ = lean_unbox(v___x_1368_);
v_kind_boxed_1381_ = lean_unbox(v_kind_1375_);
v_res_1382_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_boxed_1379_, v___x_12114__boxed_1380_, v___x_1369_, v___x_1370_, v_name_1371_, v___x_1372_, v_decl_1373_, v_stx_1374_, v_kind_boxed_1381_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v___x_1390_, uint8_t v_builtin_1391_, lean_object* v_name_1392_){
_start:
{
lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___y_1403_; 
lean_inc_n(v_name_1392_, 2);
v___f_1394_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1394_, 0, v_name_1392_);
v___x_1395_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0));
v___x_1396_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1));
v___x_1397_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1398_ = 1;
v___x_1399_ = lean_box(v_builtin_1391_);
v___x_1400_ = lean_box(v___x_1398_);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1401_, 0, v___x_1399_);
lean_closure_set(v___f_1401_, 1, v___x_1400_);
lean_closure_set(v___f_1401_, 2, v___x_1395_);
lean_closure_set(v___f_1401_, 3, v___x_1396_);
lean_closure_set(v___f_1401_, 4, v_name_1392_);
lean_closure_set(v___f_1401_, 5, v___x_1390_);
if (v_builtin_1391_ == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___y_1403_ = v___x_1426_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___y_1403_ = v___x_1427_;
goto v___jp_1402_;
}
v___jp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v_impl_1408_; lean_object* v___x_1409_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
lean_inc_ref(v___y_1403_);
v___x_1405_ = lean_string_append(v___y_1403_, v___x_1404_);
v___x_1406_ = 1;
v___x_1407_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1407_, 0, v___x_1397_);
lean_ctor_set(v___x_1407_, 1, v_name_1392_);
lean_ctor_set(v___x_1407_, 2, v___x_1405_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*3, v___x_1406_);
v_impl_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_impl_1408_, 0, v___x_1407_);
lean_ctor_set(v_impl_1408_, 1, v___f_1401_);
lean_ctor_set(v_impl_1408_, 2, v___f_1394_);
lean_inc_ref(v_impl_1408_);
v___x_1409_ = l_Lean_registerBuiltinAttribute(v_impl_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v___x_1409_, 0);
lean_dec(v_unused_1417_);
v___x_1411_ = v___x_1409_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_dec(v___x_1409_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v_impl_1408_);
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_impl_1408_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref_known(v_impl_1408_, 3);
v_a_1418_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1409_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1409_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v___x_1428_, lean_object* v_builtin_1429_, lean_object* v_name_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_builtin_boxed_1432_; lean_object* v_res_1433_; 
v_builtin_boxed_1432_ = lean_unbox(v_builtin_1429_);
v_res_1433_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1428_, v_builtin_boxed_1432_, v_name_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1441_ = lean_box(1);
v___x_1442_ = 1;
v___x_1443_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1444_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1441_, v___x_1442_, v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref_known(v___x_1444_, 1);
v___x_1445_ = 0;
v___x_1446_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1447_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1441_, v___x_1445_, v___x_1446_);
return v___x_1447_;
}
else
{
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_();
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1450_, lean_object* v_msg_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(v_00_u03b1_1456_, v_msg_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_1462_, lean_object* v_t_1463_, uint64_t v_k_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_1463_, v_k_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_){
_start:
{
uint64_t v_k_boxed_1469_; lean_object* v_res_1470_; 
v_k_boxed_1469_ = lean_unbox_uint64(v_k_1468_);
lean_dec_ref(v_k_1468_);
v_res_1470_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(v_00_u03b4_1466_, v_t_1467_, v_k_boxed_1469_);
lean_dec(v_t_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1471_, lean_object* v_name_1472_, uint8_t v_kind_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_1472_, v_kind_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_name_1481_, lean_object* v_kind_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_kind_boxed_1488_; lean_object* v_res_1489_; 
v_kind_boxed_1488_ = lean_unbox(v_kind_1482_);
v_res_1489_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(v_00_u03b1_1480_, v_name_1481_, v_kind_boxed_1488_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(lean_object* v_00_u03b1_1490_, lean_object* v_x_1491_, uint8_t v_isExporting_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1491_, v_isExporting_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object* v_00_u03b1_1499_, lean_object* v_x_1500_, lean_object* v_isExporting_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v_isExporting_boxed_1507_; lean_object* v_res_1508_; 
v_isExporting_boxed_1507_ = lean_unbox(v_isExporting_1501_);
v_res_1508_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(v_00_u03b1_1499_, v_x_1500_, v_isExporting_boxed_1507_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1509_, lean_object* v_x_1510_, uint8_t v_when_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1510_, v_when_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_x_1519_, lean_object* v_when_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_when_boxed_1526_; lean_object* v_res_1527_; 
v_when_boxed_1526_ = lean_unbox(v_when_1520_);
v_res_1527_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(v_00_u03b1_1518_, v_x_1519_, v_when_boxed_1526_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_msg_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1536_, v_msg_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
if (lean_obj_tag(v_a_1544_) == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_array_to_list(v_a_1545_);
return v___x_1546_;
}
else
{
lean_object* v_head_1547_; lean_object* v_tail_1548_; lean_object* v___x_1549_; 
v_head_1547_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_head_1547_);
v_tail_1548_ = lean_ctor_get(v_a_1544_, 1);
lean_inc(v_tail_1548_);
lean_dec_ref_known(v_a_1544_, 2);
v___x_1549_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1545_, v_head_1547_);
v_a_1544_ = v_tail_1548_;
v_a_1545_ = v___x_1549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object* v_x_1555_){
_start:
{
uint64_t v_hash_1556_; lean_object* v_pos_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_hash_1556_ = lean_ctor_get_uint64(v_x_1555_, sizeof(void*)*1);
v_pos_1557_ = lean_ctor_get(v_x_1555_, 0);
lean_inc_ref(v_pos_1557_);
lean_dec_ref(v_x_1555_);
v___x_1558_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
v___x_1559_ = lean_uint64_to_nat(v_hash_1556_);
v___x_1560_ = l_Lean_bignumToJson(v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1558_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1565_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_1557_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v___x_1562_);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1562_);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1563_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1571_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1569_, v___x_1570_);
v___x_1572_ = l_Lean_Json_mkObj(v___x_1571_);
lean_dec(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object* v_j_1575_, lean_object* v_k_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = l_Lean_Json_getObjValD(v_j_1575_, v_k_1576_);
v___x_1578_ = l_Lean_UInt64_fromJson_x3f(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object* v_j_1579_, lean_object* v_k_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_j_1579_, v_k_1580_);
lean_dec_ref(v_k_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object* v_j_1582_, lean_object* v_k_1583_){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = l_Lean_Json_getObjValD(v_j_1582_, v_k_1583_);
v___x_1585_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object* v_j_1586_, lean_object* v_k_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_j_1586_, v_k_1587_);
lean_dec_ref(v_k_1587_);
return v_res_1588_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = 1;
v___x_1595_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1));
v___x_1596_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1598_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2);
v___x_1599_ = lean_string_append(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = 1;
v___x_1603_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4));
v___x_1604_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5);
v___x_1606_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1607_ = lean_string_append(v___x_1606_, v___x_1605_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1610_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6);
v___x_1611_ = lean_string_append(v___x_1610_, v___x_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = 1;
v___x_1615_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9));
v___x_1616_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1615_, v___x_1614_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10);
v___x_1618_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1619_ = lean_string_append(v___x_1618_, v___x_1617_);
return v___x_1619_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1621_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11);
v___x_1622_ = lean_string_append(v___x_1621_, v___x_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object* v_json_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
lean_inc(v_json_1623_);
v___x_1625_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_json_1623_, v___x_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_json_1623_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1630_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8);
v___x_1631_ = lean_string_append(v___x_1630_, v_a_1626_);
lean_dec(v_a_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1631_);
v___x_1633_ = v___x_1628_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1637_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1638_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_json_1623_, v___x_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1636_);
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
v___x_1643_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12);
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
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1658_; 
v_a_1649_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1651_ = v___x_1638_;
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1638_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; uint64_t v___x_1654_; lean_object* v___x_1656_; 
v___x_1653_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1653_, 0, v_a_1649_);
v___x_1654_ = lean_unbox_uint64(v_a_1636_);
lean_dec(v_a_1636_);
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
lean_dec(v___x_1672_);
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
v___x_1691_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
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
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object* v___y_1728_){
_start:
{
lean_object* v_doc_1730_; lean_object* v___x_1731_; 
v_doc_1730_ = lean_ctor_get(v___y_1728_, 1);
lean_inc_ref(v_doc_1730_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_doc_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1732_);
lean_dec_ref(v___y_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t v_k_1735_, lean_object* v_t_1736_){
_start:
{
if (lean_obj_tag(v_t_1736_) == 0)
{
lean_object* v_k_1737_; lean_object* v_l_1738_; lean_object* v_r_1739_; uint64_t v___x_1740_; uint8_t v___x_1741_; 
v_k_1737_ = lean_ctor_get(v_t_1736_, 1);
v_l_1738_ = lean_ctor_get(v_t_1736_, 3);
v_r_1739_ = lean_ctor_get(v_t_1736_, 4);
v___x_1740_ = lean_unbox_uint64(v_k_1737_);
v___x_1741_ = lean_uint64_dec_lt(v_k_1735_, v___x_1740_);
if (v___x_1741_ == 0)
{
uint64_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = lean_unbox_uint64(v_k_1737_);
v___x_1743_ = lean_uint64_dec_eq(v_k_1735_, v___x_1742_);
if (v___x_1743_ == 0)
{
v_t_1736_ = v_r_1739_;
goto _start;
}
else
{
return v___x_1743_;
}
}
else
{
v_t_1736_ = v_l_1738_;
goto _start;
}
}
else
{
uint8_t v___x_1746_; 
v___x_1746_ = 0;
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object* v_k_1747_, lean_object* v_t_1748_){
_start:
{
uint64_t v_k_boxed_1749_; uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_k_boxed_1749_ = lean_unbox_uint64(v_k_1747_);
lean_dec_ref(v_k_1747_);
v_res_1750_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_boxed_1749_, v_t_1748_);
lean_dec(v_t_1748_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object* v___x_1752_, uint64_t v_hash_1753_, lean_object* v_s_1754_){
_start:
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1754_);
v___x_1756_ = lean_nat_dec_le(v___x_1752_, v___x_1755_);
lean_dec(v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v_toEnvExtension_1758_; lean_object* v_asyncMode_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1757_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1758_ = lean_ctor_get(v___x_1757_, 0);
v_asyncMode_1759_ = lean_ctor_get(v_toEnvExtension_1758_, 2);
v___x_1760_ = lean_box(1);
v___x_1761_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_1754_);
v___x_1762_ = lean_box(0);
v___x_1763_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1760_, v___x_1757_, v___x_1761_, v_asyncMode_1759_, v___x_1762_);
v___x_1764_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_hash_1753_, v___x_1763_);
lean_dec(v___x_1763_);
return v___x_1764_;
}
else
{
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object* v___x_1765_, lean_object* v_hash_1766_, lean_object* v_s_1767_){
_start:
{
uint64_t v_hash_boxed_1768_; uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_hash_boxed_1768_ = lean_unbox_uint64(v_hash_1766_);
lean_dec_ref(v_hash_1766_);
v_res_1769_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1765_, v_hash_boxed_1768_, v_s_1767_);
lean_dec_ref(v_s_1767_);
lean_dec(v___x_1765_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object* v___x_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object* v___x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1775_, v___y_1776_);
lean_dec_ref(v___y_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object* v_snd_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_snd_1779_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1798_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1798_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1798_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_javascript_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v_javascript_1793_ = lean_ctor_get(v_a_1789_, 0);
lean_inc_ref(v_javascript_1793_);
lean_dec(v_a_1789_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_javascript_1793_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1794_);
v___x_1796_ = v___x_1791_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_a_1799_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1788_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1788_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object* v_snd_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t v_hash_1817_, lean_object* v___x_1818_, lean_object* v_snap_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v_toEnvExtension_1823_; lean_object* v_asyncMode_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1822_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1823_ = lean_ctor_get(v___x_1822_, 0);
v_asyncMode_1824_ = lean_ctor_get(v_toEnvExtension_1823_, 2);
v___x_1825_ = lean_box(1);
v___x_1826_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1819_);
v___x_1827_ = lean_box(0);
v___x_1828_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1825_, v___x_1822_, v___x_1826_, v_asyncMode_1824_, v___x_1827_);
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1828_, v_hash_1817_);
lean_dec(v___x_1828_);
if (lean_obj_tag(v___x_1829_) == 1)
{
lean_object* v_val_1830_; lean_object* v_snd_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; 
lean_dec_ref(v___x_1818_);
v_val_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v_snd_1831_ = lean_ctor_get(v_val_1830_, 1);
lean_inc(v_snd_1831_);
lean_dec(v_val_1830_);
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__2___boxed), 9, 1);
lean_closure_set(v___f_1832_, 0, v_snd_1831_);
v___x_1833_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1819_, v___f_1832_, v___y_1820_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; 
lean_dec(v___x_1829_);
lean_dec_ref(v_snap_1819_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1818_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object* v_hash_1835_, lean_object* v___x_1836_, lean_object* v_snap_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint64_t v_hash_boxed_1840_; lean_object* v_res_1841_; 
v_hash_boxed_1840_ = lean_unbox_uint64(v_hash_1835_);
lean_dec_ref(v_hash_1835_);
v_res_1841_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_boxed_1840_, v___x_1836_, v_snap_1837_, v___y_1838_);
lean_dec_ref(v___y_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource(lean_object* v_args_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint64_t v_hash_1849_; lean_object* v_pos_1850_; lean_object* v___x_1851_; 
v___x_1847_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1848_ = lean_st_ref_get(v___x_1847_);
v_hash_1849_ = lean_ctor_get_uint64(v_args_1844_, sizeof(void*)*1);
v_pos_1850_ = lean_ctor_get(v_args_1844_, 0);
lean_inc_ref(v_pos_1850_);
lean_dec_ref(v_args_1844_);
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1848_, v_hash_1849_);
lean_dec(v___x_1848_);
if (lean_obj_tag(v___x_1851_) == 1)
{
lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v_pos_1850_);
v_val_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1863_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1863_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_snd_1856_; lean_object* v_javascript_1857_; lean_object* v___x_1859_; 
v_snd_1856_ = lean_ctor_get(v_val_1852_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_val_1852_);
v_javascript_1857_ = lean_ctor_get(v_snd_1856_, 0);
lean_inc_ref(v_javascript_1857_);
lean_dec(v_snd_1856_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_javascript_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_javascript_1857_);
v___x_1859_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_task_pure(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v_toEditableDocumentCore_1866_; lean_object* v_meta_1867_; lean_object* v_text_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___f_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___f_1882_; lean_object* v___x_1883_; 
lean_dec(v___x_1851_);
v___x_1864_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_1845_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v_toEditableDocumentCore_1866_ = lean_ctor_get(v_a_1865_, 0);
v_meta_1867_ = lean_ctor_get(v_toEditableDocumentCore_1866_, 0);
v_text_1868_ = lean_ctor_get(v_meta_1867_, 3);
v___x_1869_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1868_, v_pos_1850_);
v___x_1870_ = lean_box_uint64(v_hash_1849_);
v___f_1871_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1871_, 0, v___x_1869_);
lean_closure_set(v___f_1871_, 1, v___x_1870_);
v___x_1872_ = 3;
v___x_1873_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_1874_ = lean_uint64_to_nat(v_hash_1849_);
v___x_1875_ = l_Nat_reprFast(v___x_1874_);
v___x_1876_ = lean_string_append(v___x_1873_, v___x_1875_);
lean_dec_ref(v___x_1875_);
v___x_1877_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_1878_ = lean_string_append(v___x_1876_, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*1, v___x_1872_);
lean_inc_ref(v___x_1879_);
v___f_1880_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1880_, 0, v___x_1879_);
v___x_1881_ = lean_box_uint64(v_hash_1849_);
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1882_, 0, v___x_1881_);
lean_closure_set(v___f_1882_, 1, v___x_1879_);
v___x_1883_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1865_, v___f_1871_, v___f_1880_, v___f_1882_, v_a_1845_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object* v_args_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Widget_getWidgetSource(v_args_1884_, v_a_1885_);
lean_dec_ref(v_a_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object* v_00_u03b2_1888_, uint64_t v_k_1889_, lean_object* v_t_1890_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1889_, v_t_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object* v_00_u03b2_1892_, lean_object* v_k_1893_, lean_object* v_t_1894_){
_start:
{
uint64_t v_k_boxed_1895_; uint8_t v_res_1896_; lean_object* v_r_1897_; 
v_k_boxed_1895_ = lean_unbox_uint64(v_k_1893_);
lean_dec_ref(v_k_1893_);
v_res_1896_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(v_00_u03b2_1892_, v_k_boxed_1895_, v_t_1894_);
lean_dec(v_t_1894_);
v_r_1897_ = lean_box(v_res_1896_);
return v_r_1897_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_1898_, lean_object* v_i_1899_, lean_object* v_k_1900_){
_start:
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = lean_array_get_size(v_keys_1898_);
v___x_1902_ = lean_nat_dec_lt(v_i_1899_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_dec(v_i_1899_);
return v___x_1902_;
}
else
{
lean_object* v_k_x27_1903_; uint8_t v___x_1904_; 
v_k_x27_1903_ = lean_array_fget_borrowed(v_keys_1898_, v_i_1899_);
v___x_1904_ = lean_name_eq(v_k_1900_, v_k_x27_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_i_1899_, v___x_1905_);
lean_dec(v_i_1899_);
v_i_1899_ = v___x_1906_;
goto _start;
}
else
{
lean_dec(v_i_1899_);
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_1908_, lean_object* v_i_1909_, lean_object* v_k_1910_){
_start:
{
uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_res_1911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1908_, v_i_1909_, v_k_1910_);
lean_dec(v_k_1910_);
lean_dec_ref(v_keys_1908_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_1913_, size_t v_x_1914_, lean_object* v_x_1915_){
_start:
{
if (lean_obj_tag(v_x_1913_) == 0)
{
lean_object* v_es_1916_; lean_object* v___x_1917_; size_t v___x_1918_; size_t v___x_1919_; lean_object* v_j_1920_; lean_object* v___x_1921_; 
v_es_1916_ = lean_ctor_get(v_x_1913_, 0);
v___x_1917_ = lean_box(2);
v___x_1918_ = ((size_t)31ULL);
v___x_1919_ = lean_usize_land(v_x_1914_, v___x_1918_);
v_j_1920_ = lean_usize_to_nat(v___x_1919_);
v___x_1921_ = lean_array_get_borrowed(v___x_1917_, v_es_1916_, v_j_1920_);
lean_dec(v_j_1920_);
switch(lean_obj_tag(v___x_1921_))
{
case 0:
{
lean_object* v_key_1922_; uint8_t v___x_1923_; 
v_key_1922_ = lean_ctor_get(v___x_1921_, 0);
v___x_1923_ = lean_name_eq(v_x_1915_, v_key_1922_);
return v___x_1923_;
}
case 1:
{
lean_object* v_node_1924_; size_t v___x_1925_; size_t v___x_1926_; 
v_node_1924_ = lean_ctor_get(v___x_1921_, 0);
v___x_1925_ = ((size_t)5ULL);
v___x_1926_ = lean_usize_shift_right(v_x_1914_, v___x_1925_);
v_x_1913_ = v_node_1924_;
v_x_1914_ = v___x_1926_;
goto _start;
}
default: 
{
uint8_t v___x_1928_; 
v___x_1928_ = 0;
return v___x_1928_;
}
}
}
else
{
lean_object* v_ks_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_ks_1929_ = lean_ctor_get(v_x_1913_, 0);
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_1929_, v___x_1930_, v_x_1915_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
size_t v_x_1062__boxed_1935_; uint8_t v_res_1936_; lean_object* v_r_1937_; 
v_x_1062__boxed_1935_ = lean_unbox_usize(v_x_1933_);
lean_dec(v_x_1933_);
v_res_1936_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1932_, v_x_1062__boxed_1935_, v_x_1934_);
lean_dec(v_x_1934_);
lean_dec_ref(v_x_1932_);
v_r_1937_ = lean_box(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
uint64_t v___y_1941_; 
if (lean_obj_tag(v_x_1939_) == 0)
{
uint64_t v___x_1944_; 
v___x_1944_ = 1723ULL;
v___y_1941_ = v___x_1944_;
goto v___jp_1940_;
}
else
{
uint64_t v_hash_1945_; 
v_hash_1945_ = lean_ctor_get_uint64(v_x_1939_, sizeof(void*)*2);
v___y_1941_ = v_hash_1945_;
goto v___jp_1940_;
}
v___jp_1940_:
{
size_t v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_uint64_to_usize(v___y_1941_);
v___x_1943_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1938_, v___x_1942_, v_x_1939_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_1946_, lean_object* v_x_1947_){
_start:
{
uint8_t v_res_1948_; lean_object* v_r_1949_; 
v_res_1948_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1946_, v_x_1947_);
lean_dec(v_x_1947_);
lean_dec_ref(v_x_1946_);
v_r_1949_ = lean_box(v_res_1948_);
return v_r_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v_ks_1954_; lean_object* v_vs_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1979_; 
v_ks_1954_ = lean_ctor_get(v_x_1950_, 0);
v_vs_1955_ = lean_ctor_get(v_x_1950_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1957_ = v_x_1950_;
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_vs_1955_);
lean_inc(v_ks_1954_);
lean_dec(v_x_1950_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = lean_array_get_size(v_ks_1954_);
v___x_1960_ = lean_nat_dec_lt(v_x_1951_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec(v_x_1951_);
v___x_1961_ = lean_array_push(v_ks_1954_, v_x_1952_);
v___x_1962_ = lean_array_push(v_vs_1955_, v_x_1953_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1962_);
lean_ctor_set(v___x_1957_, 0, v___x_1961_);
v___x_1964_ = v___x_1957_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v_k_x27_1966_; uint8_t v___x_1967_; 
v_k_x27_1966_ = lean_array_fget_borrowed(v_ks_1954_, v_x_1951_);
v___x_1967_ = lean_name_eq(v_x_1952_, v_k_x27_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1969_; 
if (v_isShared_1958_ == 0)
{
v___x_1969_ = v___x_1957_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_ks_1954_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_vs_1955_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_unsigned_to_nat(1u);
v___x_1971_ = lean_nat_add(v_x_1951_, v___x_1970_);
lean_dec(v_x_1951_);
v_x_1950_ = v___x_1969_;
v_x_1951_ = v___x_1971_;
goto _start;
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = lean_array_fset(v_ks_1954_, v_x_1951_, v_x_1952_);
v___x_1975_ = lean_array_fset(v_vs_1955_, v_x_1951_, v_x_1953_);
lean_dec(v_x_1951_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1975_);
lean_ctor_set(v___x_1957_, 0, v___x_1974_);
v___x_1977_ = v___x_1957_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_n_1980_, lean_object* v_k_1981_, lean_object* v_v_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_n_1980_, v___x_1983_, v_k_1981_, v_v_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_x_1986_, size_t v_x_1987_, size_t v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 0)
{
lean_object* v_es_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v_j_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_es_1991_ = lean_ctor_get(v_x_1986_, 0);
v___x_1992_ = ((size_t)31ULL);
v___x_1993_ = lean_usize_land(v_x_1987_, v___x_1992_);
v_j_1994_ = lean_usize_to_nat(v___x_1993_);
v___x_1995_ = lean_array_get_size(v_es_1991_);
v___x_1996_ = lean_nat_dec_lt(v_j_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec(v_j_1994_);
lean_dec(v_x_1990_);
lean_dec(v_x_1989_);
return v_x_1986_;
}
else
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2035_; 
lean_inc_ref(v_es_1991_);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_x_1986_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_x_1986_, 0);
lean_dec(v_unused_2036_);
v___x_1998_ = v_x_1986_;
v_isShared_1999_ = v_isSharedCheck_2035_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v_x_1986_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2035_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_v_2000_; lean_object* v___x_2001_; lean_object* v_xs_x27_2002_; lean_object* v___y_2004_; 
v_v_2000_ = lean_array_fget(v_es_1991_, v_j_1994_);
v___x_2001_ = lean_box(0);
v_xs_x27_2002_ = lean_array_fset(v_es_1991_, v_j_1994_, v___x_2001_);
switch(lean_obj_tag(v_v_2000_))
{
case 0:
{
lean_object* v_key_2009_; lean_object* v_val_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_key_2009_ = lean_ctor_get(v_v_2000_, 0);
v_val_2010_ = lean_ctor_get(v_v_2000_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_v_2000_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2012_ = v_v_2000_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_val_2010_);
lean_inc(v_key_2009_);
lean_dec(v_v_2000_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_name_eq(v_x_1989_, v_key_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_del_object(v___x_2012_);
v___x_2015_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2009_, v_val_2010_, v_x_1989_, v_x_1990_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___y_2004_ = v___x_2016_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2018_; 
lean_dec(v_val_2010_);
lean_dec(v_key_2009_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_x_1990_);
lean_ctor_set(v___x_2012_, 0, v_x_1989_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_x_1989_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_x_1990_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
v___y_2004_ = v___x_2018_;
goto v___jp_2003_;
}
}
}
}
case 1:
{
lean_object* v_node_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2033_; 
v_node_2021_ = lean_ctor_get(v_v_2000_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_v_2000_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2023_ = v_v_2000_;
v_isShared_2024_ = v_isSharedCheck_2033_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_node_2021_);
lean_dec(v_v_2000_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2033_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2025_ = ((size_t)5ULL);
v___x_2026_ = lean_usize_shift_right(v_x_1987_, v___x_2025_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_x_1988_, v___x_2027_);
v___x_2029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_node_2021_, v___x_2026_, v___x_2028_, v_x_1989_, v_x_1990_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2029_);
v___x_2031_ = v___x_2023_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v___y_2004_ = v___x_2031_;
goto v___jp_2003_;
}
}
}
default: 
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_x_1989_);
lean_ctor_set(v___x_2034_, 1, v_x_1990_);
v___y_2004_ = v___x_2034_;
goto v___jp_2003_;
}
}
v___jp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_array_fset(v_xs_x27_2002_, v_j_1994_, v___y_2004_);
lean_dec(v_j_1994_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2005_);
v___x_2007_ = v___x_1998_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_object* v_ks_2037_; lean_object* v_vs_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2056_; 
v_ks_2037_ = lean_ctor_get(v_x_1986_, 0);
v_vs_2038_ = lean_ctor_get(v_x_1986_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_1986_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2040_ = v_x_1986_;
v_isShared_2041_ = v_isSharedCheck_2056_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_vs_2038_);
lean_inc(v_ks_2037_);
lean_dec(v_x_1986_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2056_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_ks_2037_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_vs_2038_);
v___x_2043_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v_newNode_2044_; size_t v___x_2045_; uint8_t v___x_2046_; 
v_newNode_2044_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v___x_2043_, v_x_1989_, v_x_1990_);
v___x_2045_ = ((size_t)7ULL);
v___x_2046_ = lean_usize_dec_le(v___x_2045_, v_x_1988_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2047_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2044_);
v___x_2048_ = lean_unsigned_to_nat(4u);
v___x_2049_ = lean_nat_dec_lt(v___x_2047_, v___x_2048_);
lean_dec(v___x_2047_);
if (v___x_2049_ == 0)
{
lean_object* v_ks_2050_; lean_object* v_vs_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_ks_2050_ = lean_ctor_get(v_newNode_2044_, 0);
lean_inc_ref(v_ks_2050_);
v_vs_2051_ = lean_ctor_get(v_newNode_2044_, 1);
lean_inc_ref(v_vs_2051_);
lean_dec_ref(v_newNode_2044_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0);
v___x_2054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_x_1988_, v_ks_2050_, v_vs_2051_, v___x_2052_, v___x_2053_);
lean_dec_ref(v_vs_2051_);
lean_dec_ref(v_ks_2050_);
return v___x_2054_;
}
else
{
return v_newNode_2044_;
}
}
else
{
return v_newNode_2044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t v_depth_2057_, lean_object* v_keys_2058_, lean_object* v_vals_2059_, lean_object* v_i_2060_, lean_object* v_entries_2061_){
_start:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = lean_array_get_size(v_keys_2058_);
v___x_2063_ = lean_nat_dec_lt(v_i_2060_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec(v_i_2060_);
return v_entries_2061_;
}
else
{
lean_object* v_k_2064_; lean_object* v_v_2065_; uint64_t v___y_2067_; 
v_k_2064_ = lean_array_fget_borrowed(v_keys_2058_, v_i_2060_);
v_v_2065_ = lean_array_fget_borrowed(v_vals_2059_, v_i_2060_);
if (lean_obj_tag(v_k_2064_) == 0)
{
uint64_t v___x_2078_; 
v___x_2078_ = 1723ULL;
v___y_2067_ = v___x_2078_;
goto v___jp_2066_;
}
else
{
uint64_t v_hash_2079_; 
v_hash_2079_ = lean_ctor_get_uint64(v_k_2064_, sizeof(void*)*2);
v___y_2067_ = v_hash_2079_;
goto v___jp_2066_;
}
v___jp_2066_:
{
size_t v_h_2068_; size_t v___x_2069_; lean_object* v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; size_t v_h_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_h_2068_ = lean_uint64_to_usize(v___y_2067_);
v___x_2069_ = ((size_t)5ULL);
v___x_2070_ = lean_unsigned_to_nat(1u);
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_sub(v_depth_2057_, v___x_2071_);
v___x_2073_ = lean_usize_mul(v___x_2069_, v___x_2072_);
v_h_2074_ = lean_usize_shift_right(v_h_2068_, v___x_2073_);
v___x_2075_ = lean_nat_add(v_i_2060_, v___x_2070_);
lean_dec(v_i_2060_);
lean_inc(v_v_2065_);
lean_inc(v_k_2064_);
v___x_2076_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_entries_2061_, v_h_2074_, v_depth_2057_, v_k_2064_, v_v_2065_);
v_i_2060_ = v___x_2075_;
v_entries_2061_ = v___x_2076_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_depth_2080_, lean_object* v_keys_2081_, lean_object* v_vals_2082_, lean_object* v_i_2083_, lean_object* v_entries_2084_){
_start:
{
size_t v_depth_boxed_2085_; lean_object* v_res_2086_; 
v_depth_boxed_2085_ = lean_unbox_usize(v_depth_2080_);
lean_dec(v_depth_2080_);
v_res_2086_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_boxed_2085_, v_keys_2081_, v_vals_2082_, v_i_2083_, v_entries_2084_);
lean_dec_ref(v_vals_2082_);
lean_dec_ref(v_keys_2081_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
size_t v_x_1197__boxed_2092_; size_t v_x_1198__boxed_2093_; lean_object* v_res_2094_; 
v_x_1197__boxed_2092_ = lean_unbox_usize(v_x_2088_);
lean_dec(v_x_2088_);
v_x_1198__boxed_2093_ = lean_unbox_usize(v_x_2089_);
lean_dec(v_x_2089_);
v_res_2094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2087_, v_x_1197__boxed_2092_, v_x_1198__boxed_2093_, v_x_2090_, v_x_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
uint64_t v___y_2099_; 
if (lean_obj_tag(v_x_2096_) == 0)
{
uint64_t v___x_2103_; 
v___x_2103_ = 1723ULL;
v___y_2099_ = v___x_2103_;
goto v___jp_2098_;
}
else
{
uint64_t v_hash_2104_; 
v_hash_2104_ = lean_ctor_get_uint64(v_x_2096_, sizeof(void*)*2);
v___y_2099_ = v_hash_2104_;
goto v___jp_2098_;
}
v___jp_2098_:
{
size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_uint64_to_usize(v___y_2099_);
v___x_2101_ = ((size_t)1ULL);
v___x_2102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2095_, v___x_2100_, v___x_2101_, v_x_2096_, v_x_2097_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v___y_2105_){
_start:
{
lean_inc(v___y_2105_);
return v___y_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(v___y_2106_);
lean_dec(v___y_2106_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object* v_expireTime_2108_, lean_object* v_x_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_x_2109_);
lean_ctor_set(v___x_2110_, 1, v_expireTime_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object* v_val_2111_, lean_object* v___f_2112_, lean_object* v_x_2113_, lean_object* v___y_2114_){
_start:
{
if (lean_obj_tag(v_x_2113_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___f_2112_);
v_a_2116_ = lean_ctor_get(v_x_2113_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v_x_2113_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v_x_2113_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 1);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2147_; 
v_a_2124_ = lean_ctor_get(v_x_2113_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2126_ = v_x_2113_;
v_isShared_2127_ = v_isSharedCheck_2147_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v_x_2113_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2147_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v_objects_2129_; lean_object* v_expireTime_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2146_; 
v___x_2128_ = lean_st_ref_take(v_val_2111_);
v_objects_2129_ = lean_ctor_get(v___x_2128_, 0);
v_expireTime_2130_ = lean_ctor_get(v___x_2128_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2132_ = v___x_2128_;
v_isShared_2133_ = v_isSharedCheck_2146_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_expireTime_2130_);
lean_inc(v_objects_2129_);
lean_dec(v___x_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2146_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_2134_, 0, v_expireTime_2130_);
v___x_2135_ = l_Lean_Widget_instToJsonWidgetSource_toJson(v_a_2124_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_objects_2129_);
lean_ctor_set(v___x_2132_, 0, v___x_2135_);
v___x_2137_ = v___x_2132_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_objects_2129_);
v___x_2137_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2138_ = l_Prod_map___redArg(v___f_2112_, v___f_2134_, v___x_2137_);
v_fst_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_fst_2139_);
v_snd_2140_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2140_);
lean_dec_ref(v___x_2138_);
v___x_2141_ = lean_st_ref_put(v_val_2111_, v_snd_2140_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 0);
lean_ctor_set(v___x_2126_, 0, v_fst_2139_);
v___x_2143_ = v___x_2126_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_fst_2139_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object* v_val_2148_, lean_object* v___f_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2148_, v___f_2149_, v_x_2150_, v___y_2151_);
lean_dec_ref(v___y_2151_);
lean_dec(v_val_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object* v___f_2161_, lean_object* v_method_2162_, lean_object* v_handler_2163_, uint64_t v_seshId_2164_, lean_object* v_j_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_rpcSessions_2168_; lean_object* v___x_2169_; 
v_rpcSessions_2168_ = lean_ctor_get(v___y_2166_, 0);
v___x_2169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_2168_, v_seshId_2164_);
if (lean_obj_tag(v___x_2169_) == 1)
{
lean_object* v_val_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_val_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc_n(v_val_2170_, 2);
lean_dec_ref_known(v___x_2169_, 1);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2171_, 0, v_val_2170_);
lean_closure_set(v___f_2171_, 1, v___f_2161_);
v___x_2172_ = lean_st_ref_get(v_val_2170_);
lean_dec(v_val_2170_);
lean_dec(v___x_2172_);
lean_inc(v_j_2165_);
v___x_2173_ = l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(v_j_2165_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v___f_2171_);
lean_dec_ref(v_handler_2163_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2194_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2194_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
uint8_t v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2178_ = 3;
v___x_2179_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_2180_ = 1;
v___x_2181_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2162_, v___x_2180_);
v___x_2182_ = lean_string_append(v___x_2179_, v___x_2181_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_2184_ = lean_string_append(v___x_2182_, v___x_2183_);
v___x_2185_ = l_Lean_Json_compress(v_j_2165_);
v___x_2186_ = lean_string_append(v___x_2184_, v___x_2185_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_2188_ = lean_string_append(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_string_append(v___x_2188_, v_a_2174_);
lean_dec(v_a_2174_);
v___x_2190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v___x_2178_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 1);
lean_ctor_set(v___x_2176_, 0, v___x_2190_);
v___x_2192_ = v___x_2176_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
lean_dec(v_j_2165_);
lean_dec(v_method_2162_);
v_a_2195_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2173_, 1);
lean_inc_ref(v___y_2166_);
v___x_2196_ = lean_apply_3(v_handler_2163_, v_a_2195_, v___y_2166_, lean_box(0));
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_2197_, v___f_2171_, v___y_2166_);
return v___x_2198_;
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v___f_2171_);
v_a_2199_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2196_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2196_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v___x_2169_);
lean_dec(v_j_2165_);
lean_dec_ref(v_handler_2163_);
lean_dec(v_method_2162_);
lean_dec_ref(v___f_2161_);
v___x_2207_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object* v___f_2209_, lean_object* v_method_2210_, lean_object* v_handler_2211_, lean_object* v_seshId_2212_, lean_object* v_j_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint64_t v_seshId_boxed_2216_; lean_object* v_res_2217_; 
v_seshId_boxed_2216_ = lean_unbox_uint64(v_seshId_2212_);
lean_dec_ref(v_seshId_2212_);
v_res_2217_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v___f_2209_, v_method_2210_, v_handler_2211_, v_seshId_boxed_2216_, v_j_2213_, v___y_2214_);
lean_dec_ref(v___y_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_method_2219_, lean_object* v_handler_2220_){
_start:
{
lean_object* v___f_2221_; lean_object* v___f_2222_; 
v___f_2221_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_2222_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed), 7, 3);
lean_closure_set(v___f_2222_, 0, v___f_2221_);
lean_closure_set(v___f_2222_, 1, v_method_2219_);
lean_closure_set(v___f_2222_, 2, v_handler_2220_);
return v___f_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object* v_method_2227_, lean_object* v_handler_2228_){
_start:
{
lean_object* v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_errMsg_2235_; uint8_t v___x_2236_; 
v___x_2230_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_2231_ = 1;
lean_inc(v_method_2227_);
v___x_2232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2227_, v___x_2231_);
v___x_2233_ = lean_string_append(v___x_2230_, v___x_2232_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_2235_ = lean_string_append(v___x_2233_, v___x_2234_);
v___x_2236_ = l_Lean_initializing();
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_handler_2228_);
lean_dec(v_method_2227_);
v___x_2237_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_2238_ = lean_string_append(v_errMsg_2235_, v___x_2237_);
v___x_2239_ = lean_mk_io_user_error(v___x_2238_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_2242_ = lean_st_ref_get(v___x_2241_);
v___x_2243_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2242_, v_method_2227_);
lean_dec(v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v_errMsg_2235_);
lean_inc(v_method_2227_);
v___x_2244_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(v_method_2227_, v_handler_2228_);
v___x_2245_ = lean_st_ref_take(v___x_2241_);
v___x_2246_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2245_, v_method_2227_, v___x_2244_);
v___x_2247_ = lean_st_ref_put(v___x_2241_, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v_handler_2228_);
lean_dec(v_method_2227_);
v___x_2249_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_2250_ = lean_string_append(v_errMsg_2235_, v___x_2249_);
v___x_2251_ = lean_mk_io_user_error(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2253_, lean_object* v_handler_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2253_, v_handler_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2265_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2266_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v___x_2264_, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
return v_res_2268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
uint8_t v___x_2272_; 
v___x_2272_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2270_, v_x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_){
_start:
{
uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_res_2276_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2273_, v_x_2274_, v_x_2275_);
lean_dec(v_x_2275_);
lean_dec_ref(v_x_2274_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_2278_){
_start:
{
lean_inc_ref(v_x_2278_);
return v_x_2278_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2279_);
lean_dec_ref(v_x_2279_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2281_, lean_object* v_x_2282_, lean_object* v___y_2283_){
_start:
{
lean_inc_ref(v_x_2282_);
return v_x_2282_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2284_, lean_object* v_x_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b1_2284_, v_x_2285_, v___y_2286_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_x_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2289_, v_x_2290_, v_x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2293_, lean_object* v_x_2294_, size_t v_x_2295_, lean_object* v_x_2296_){
_start:
{
uint8_t v___x_2297_; 
v___x_2297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2294_, v_x_2295_, v_x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2298_, lean_object* v_x_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
size_t v_x_1681__boxed_2302_; uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_x_1681__boxed_2302_ = lean_unbox_usize(v_x_2300_);
lean_dec(v_x_2300_);
v_res_2303_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2298_, v_x_2299_, v_x_1681__boxed_2302_, v_x_2301_);
lean_dec(v_x_2301_);
lean_dec_ref(v_x_2299_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2305_, lean_object* v_x_2306_, size_t v_x_2307_, size_t v_x_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2306_, v_x_2307_, v_x_2308_, v_x_2309_, v_x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
size_t v_x_1692__boxed_2318_; size_t v_x_1693__boxed_2319_; lean_object* v_res_2320_; 
v_x_1692__boxed_2318_ = lean_unbox_usize(v_x_2314_);
lean_dec(v_x_2314_);
v_x_1693__boxed_2319_ = lean_unbox_usize(v_x_2315_);
lean_dec(v_x_2315_);
v_res_2320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_2312_, v_x_2313_, v_x_1692__boxed_2318_, v_x_1693__boxed_2319_, v_x_2316_, v_x_2317_);
return v_res_2320_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2321_, lean_object* v_keys_2322_, lean_object* v_vals_2323_, lean_object* v_heq_2324_, lean_object* v_i_2325_, lean_object* v_k_2326_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2322_, v_i_2325_, v_k_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2328_, lean_object* v_keys_2329_, lean_object* v_vals_2330_, lean_object* v_heq_2331_, lean_object* v_i_2332_, lean_object* v_k_2333_){
_start:
{
uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_res_2334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2328_, v_keys_2329_, v_vals_2330_, v_heq_2331_, v_i_2332_, v_k_2333_);
lean_dec(v_k_2333_);
lean_dec_ref(v_vals_2330_);
lean_dec_ref(v_keys_2329_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_2336_, lean_object* v_n_2337_, lean_object* v_k_2338_, lean_object* v_v_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v_n_2337_, v_k_2338_, v_v_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2341_, size_t v_depth_2342_, lean_object* v_keys_2343_, lean_object* v_vals_2344_, lean_object* v_heq_2345_, lean_object* v_i_2346_, lean_object* v_entries_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2342_, v_keys_2343_, v_vals_2344_, v_i_2346_, v_entries_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2349_, lean_object* v_depth_2350_, lean_object* v_keys_2351_, lean_object* v_vals_2352_, lean_object* v_heq_2353_, lean_object* v_i_2354_, lean_object* v_entries_2355_){
_start:
{
size_t v_depth_boxed_2356_; lean_object* v_res_2357_; 
v_depth_boxed_2356_ = lean_unbox_usize(v_depth_2350_);
lean_dec(v_depth_2350_);
v_res_2357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(v_00_u03b2_2349_, v_depth_boxed_2356_, v_keys_2351_, v_vals_2352_, v_heq_2353_, v_i_2354_, v_entries_2355_);
lean_dec_ref(v_vals_2352_);
lean_dec_ref(v_keys_2351_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_2358_, lean_object* v_x_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_x_2359_, v_x_2360_, v_x_2361_, v_x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(lean_object* v_x_2364_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_obj_tag_nat(v_x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl___boxed(lean_object* v_x_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(v_x_2366_);
lean_dec_ref(v_x_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object* v_t_2368_, lean_object* v_k_2369_){
_start:
{
if (lean_obj_tag(v_t_2368_) == 0)
{
lean_object* v_n_2370_; lean_object* v___x_2371_; 
v_n_2370_ = lean_ctor_get(v_t_2368_, 0);
lean_inc(v_n_2370_);
lean_dec_ref_known(v_t_2368_, 1);
v___x_2371_ = lean_apply_1(v_k_2369_, v_n_2370_);
return v___x_2371_;
}
else
{
lean_object* v_wi_2372_; lean_object* v___x_2373_; 
v_wi_2372_ = lean_ctor_get(v_t_2368_, 0);
lean_inc_ref(v_wi_2372_);
lean_dec_ref_known(v_t_2368_, 1);
v___x_2373_ = lean_apply_1(v_k_2369_, v_wi_2372_);
return v___x_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object* v_motive_2374_, lean_object* v_ctorIdx_2375_, lean_object* v_t_2376_, lean_object* v_h_2377_, lean_object* v_k_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2376_, v_k_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object* v_motive_2380_, lean_object* v_ctorIdx_2381_, lean_object* v_t_2382_, lean_object* v_h_2383_, lean_object* v_k_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(v_motive_2380_, v_ctorIdx_2381_, v_t_2382_, v_h_2383_, v_k_2384_);
lean_dec(v_ctorIdx_2381_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object* v_t_2386_, lean_object* v_global_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2386_, v_global_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object* v_motive_2389_, lean_object* v_t_2390_, lean_object* v_h_2391_, lean_object* v_global_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2390_, v_global_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object* v_t_2394_, lean_object* v_local_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2394_, v_local_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object* v_motive_2397_, lean_object* v_t_2398_, lean_object* v_h_2399_, lean_object* v_local_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2398_, v_local_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2402_, uint64_t v_k_2403_, lean_object* v_fallback_2404_){
_start:
{
if (lean_obj_tag(v_t_2402_) == 0)
{
lean_object* v_k_2405_; lean_object* v_v_2406_; lean_object* v_l_2407_; lean_object* v_r_2408_; uint64_t v___x_2409_; uint8_t v___x_2410_; 
v_k_2405_ = lean_ctor_get(v_t_2402_, 1);
v_v_2406_ = lean_ctor_get(v_t_2402_, 2);
v_l_2407_ = lean_ctor_get(v_t_2402_, 3);
v_r_2408_ = lean_ctor_get(v_t_2402_, 4);
v___x_2409_ = lean_unbox_uint64(v_k_2405_);
v___x_2410_ = lean_uint64_dec_lt(v_k_2403_, v___x_2409_);
if (v___x_2410_ == 0)
{
uint64_t v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = lean_unbox_uint64(v_k_2405_);
v___x_2412_ = lean_uint64_dec_eq(v_k_2403_, v___x_2411_);
if (v___x_2412_ == 0)
{
v_t_2402_ = v_r_2408_;
goto _start;
}
else
{
lean_inc(v_v_2406_);
return v_v_2406_;
}
}
else
{
v_t_2402_ = v_l_2407_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2404_);
return v_fallback_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2415_, lean_object* v_k_2416_, lean_object* v_fallback_2417_){
_start:
{
uint64_t v_k_boxed_2418_; lean_object* v_res_2419_; 
v_k_boxed_2418_ = lean_unbox_uint64(v_k_2416_);
lean_dec_ref(v_k_2416_);
v_res_2419_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2415_, v_k_boxed_2418_, v_fallback_2417_);
lean_dec(v_fallback_2417_);
lean_dec(v_t_2415_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_s_2420_, lean_object* v_x_2421_){
_start:
{
lean_object* v_fst_2422_; lean_object* v_snd_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2436_; 
v_fst_2422_ = lean_ctor_get(v_x_2421_, 0);
v_snd_2423_ = lean_ctor_get(v_x_2421_, 1);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_x_2421_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2425_ = v_x_2421_;
v_isShared_2426_ = v_isSharedCheck_2436_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_snd_2423_);
lean_inc(v_fst_2422_);
lean_dec(v_x_2421_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2436_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; uint64_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_snd_2423_);
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_unbox_uint64(v_fst_2422_);
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_s_2420_, v___x_2429_, v___x_2428_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set_tag(v___x_2425_, 1);
lean_ctor_set(v___x_2425_, 1, v___x_2430_);
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2432_ = v___x_2425_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
uint64_t v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_unbox_uint64(v_fst_2422_);
lean_dec(v_fst_2422_);
v___x_2434_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_2433_, v___x_2432_, v_s_2420_);
return v___x_2434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_x_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2439_, 0, v_a_2438_);
lean_inc_ref_n(v___x_2439_, 2);
v___x_2440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
lean_ctor_set(v___x_2440_, 2, v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_x_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v_x_2441_, v_a_2442_);
lean_dec_ref(v_x_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v___y_2444_){
_start:
{
lean_inc(v___y_2444_);
return v___y_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v___y_2445_);
lean_dec(v___y_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_));
v___x_2464_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2467_, lean_object* v_t_2468_, uint64_t v_k_2469_, lean_object* v_fallback_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2468_, v_k_2469_, v_fallback_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2472_, lean_object* v_t_2473_, lean_object* v_k_2474_, lean_object* v_fallback_2475_){
_start:
{
uint64_t v_k_boxed_2476_; lean_object* v_res_2477_; 
v_k_boxed_2476_ = lean_unbox_uint64(v_k_2474_);
lean_dec_ref(v_k_2474_);
v_res_2477_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(v_00_u03b4_2472_, v_t_2473_, v_k_boxed_2476_, v_fallback_2475_);
lean_dec(v_fallback_2475_);
lean_dec(v_t_2473_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(lean_object* v_as_x27_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
if (lean_obj_tag(v_as_x27_2478_) == 0)
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_b_2479_);
return v___x_2485_;
}
else
{
lean_object* v_head_2486_; 
v_head_2486_ = lean_ctor_get(v_as_x27_2478_, 0);
if (lean_obj_tag(v_head_2486_) == 0)
{
lean_object* v_tail_2487_; lean_object* v_n_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_tail_2487_ = lean_ctor_get(v_as_x27_2478_, 1);
v_n_2488_ = lean_ctor_get(v_head_2486_, 0);
v___x_2489_ = lean_box(0);
lean_inc(v_n_2488_);
v___x_2490_ = l_Lean_mkConst(v_n_2488_, v___x_2489_);
v___x_2491_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v___x_2490_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = lean_array_push(v_b_2479_, v_a_2492_);
v_as_x27_2478_ = v_tail_2487_;
v_b_2479_ = v___x_2493_;
goto _start;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_b_2479_);
v_a_2495_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2491_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2491_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_tail_2503_; lean_object* v_wi_2504_; lean_object* v___x_2505_; 
v_tail_2503_ = lean_ctor_get(v_as_x27_2478_, 1);
v_wi_2504_ = lean_ctor_get(v_head_2486_, 0);
lean_inc_ref(v_wi_2504_);
v___x_2505_ = lean_array_push(v_b_2479_, v_wi_2504_);
v_as_x27_2478_ = v_tail_2503_;
v_b_2479_ = v___x_2505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg___boxed(lean_object* v_as_x27_2507_, lean_object* v_b_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2507_, v_b_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v_as_x27_2507_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(lean_object* v_init_2515_, lean_object* v_x_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_v_2522_; lean_object* v_l_2523_; lean_object* v_r_2524_; lean_object* v___x_2525_; 
v_v_2522_ = lean_ctor_get(v_x_2516_, 2);
v_l_2523_ = lean_ctor_get(v_x_2516_, 3);
v_r_2524_ = lean_ctor_get(v_x_2516_, 4);
v___x_2525_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2515_, v_l_2523_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v_a_2527_; lean_object* v___x_2528_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v_a_2527_ = lean_ctor_get(v_a_2526_, 0);
lean_inc(v_a_2527_);
lean_dec(v_a_2526_);
v___x_2528_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_v_2522_, v_a_2527_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v_init_2515_ = v_a_2529_;
v_x_2516_ = v_r_2524_;
goto _start;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2528_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2528_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
return v___x_2525_;
}
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_init_2515_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1___boxed(lean_object* v_init_2541_, lean_object* v_x_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2541_, v_x_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v_x_2542_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets(lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_ret_2556_; lean_object* v___x_2557_; lean_object* v_env_2558_; lean_object* v___x_2559_; lean_object* v_ext_2560_; lean_object* v_toEnvExtension_2561_; lean_object* v_asyncMode_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_ret_2556_ = ((lean_object*)(l_Lean_Widget_evalPanelWidgets___closed__0));
v___x_2557_ = lean_st_ref_get(v_a_2554_);
v_env_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc_ref(v_env_2558_);
lean_dec(v___x_2557_);
v___x_2559_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v_ext_2560_ = lean_ctor_get(v___x_2559_, 1);
v_toEnvExtension_2561_ = lean_ctor_get(v_ext_2560_, 0);
v_asyncMode_2562_ = lean_ctor_get(v_toEnvExtension_2561_, 2);
v___x_2563_ = lean_box(1);
v___x_2564_ = 0;
v___x_2565_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2563_, v___x_2559_, v_env_2558_, v_asyncMode_2562_, v___x_2564_);
v___x_2566_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_ret_2556_, v___x_2565_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_a_2571_; lean_object* v___x_2573_; 
v_a_2571_ = lean_ctor_get(v_a_2567_, 0);
lean_inc(v_a_2571_);
lean_dec(v_a_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v_a_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2566_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2566_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Widget_evalPanelWidgets(v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object* v_as_2590_, lean_object* v_as_x27_2591_, lean_object* v_b_2592_, lean_object* v_a_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2591_, v_b_2592_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object* v_as_2600_, lean_object* v_as_x27_2601_, lean_object* v_b_2602_, lean_object* v_a_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2600_, v_as_x27_2601_, v_b_2602_, v_a_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v_as_x27_2601_);
lean_dec(v_as_2600_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, uint64_t v_h_2613_, lean_object* v_n_2614_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2615_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2616_ = lean_box_uint64(v_h_2613_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v_n_2614_);
v___x_2618_ = 0;
v___x_2619_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2610_, v_inst_2612_, v_inst_2611_, v___x_2615_, v___x_2617_, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_h_2623_, lean_object* v_n_2624_){
_start:
{
uint64_t v_h_boxed_2625_; lean_object* v_res_2626_; 
v_h_boxed_2625_ = lean_unbox_uint64(v_h_2623_);
lean_dec_ref(v_h_2623_);
v_res_2626_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2620_, v_inst_2621_, v_inst_2622_, v_h_boxed_2625_, v_n_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object* v_m_2627_, lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, uint64_t v_h_2631_, lean_object* v_n_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2628_, v_inst_2629_, v_inst_2630_, v_h_2631_, v_n_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object* v_m_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_h_2638_, lean_object* v_n_2639_){
_start:
{
uint64_t v_h_boxed_2640_; lean_object* v_res_2641_; 
v_h_boxed_2640_ = lean_unbox_uint64(v_h_2638_);
lean_dec_ref(v_h_2638_);
v_res_2641_ = l_Lean_Widget_addPanelWidgetGlobal(v_m_2634_, v_inst_2635_, v_inst_2636_, v_inst_2637_, v_h_boxed_2640_, v_n_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_inst_2644_, uint64_t v_h_2645_, lean_object* v_n_2646_){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2647_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2648_ = lean_box_uint64(v_h_2645_);
v___x_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
lean_ctor_set(v___x_2649_, 1, v_n_2646_);
v___x_2650_ = 2;
v___x_2651_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2642_, v_inst_2644_, v_inst_2643_, v___x_2647_, v___x_2649_, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_h_2655_, lean_object* v_n_2656_){
_start:
{
uint64_t v_h_boxed_2657_; lean_object* v_res_2658_; 
v_h_boxed_2657_ = lean_unbox_uint64(v_h_2655_);
lean_dec_ref(v_h_2655_);
v_res_2658_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2652_, v_inst_2653_, v_inst_2654_, v_h_boxed_2657_, v_n_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object* v_m_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, uint64_t v_h_2663_, lean_object* v_n_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2660_, v_inst_2661_, v_inst_2662_, v_h_2663_, v_n_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object* v_m_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_h_2670_, lean_object* v_n_2671_){
_start:
{
uint64_t v_h_boxed_2672_; lean_object* v_res_2673_; 
v_h_boxed_2672_ = lean_unbox_uint64(v_h_2670_);
lean_dec_ref(v_h_2670_);
v_res_2673_ = l_Lean_Widget_addPanelWidgetScoped(v_m_2666_, v_inst_2667_, v_inst_2668_, v_inst_2669_, v_h_boxed_2672_, v_n_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t v_x_2674_, uint64_t v_y_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_uint64_dec_lt(v_x_2674_, v_y_2675_);
if (v___x_2676_ == 0)
{
uint8_t v___x_2677_; 
v___x_2677_ = lean_uint64_dec_eq(v_x_2674_, v_y_2675_);
if (v___x_2677_ == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = 2;
return v___x_2678_;
}
else
{
uint8_t v___x_2679_; 
v___x_2679_ = 1;
return v___x_2679_;
}
}
else
{
uint8_t v___x_2680_; 
v___x_2680_ = 0;
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object* v_x_2681_, lean_object* v_y_2682_){
_start:
{
uint64_t v_x_boxed_2683_; uint64_t v_y_boxed_2684_; uint8_t v_res_2685_; lean_object* v_r_2686_; 
v_x_boxed_2683_ = lean_unbox_uint64(v_x_2681_);
lean_dec_ref(v_x_2681_);
v_y_boxed_2684_ = lean_unbox_uint64(v_y_2682_);
lean_dec_ref(v_y_2682_);
v_res_2685_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_boxed_2683_, v_y_boxed_2684_);
v_r_2686_ = lean_box(v_res_2685_);
return v_r_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object* v_wi_2687_, lean_object* v___f_2688_, lean_object* v_s_2689_){
_start:
{
uint64_t v_javascriptHash_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_javascriptHash_2690_ = lean_ctor_get_uint64(v_wi_2687_, sizeof(void*)*2);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_wi_2687_);
v___x_2692_ = lean_box(0);
v___x_2693_ = lean_box_uint64(v_javascriptHash_2690_);
lean_inc(v_s_2689_);
lean_inc_ref(v___f_2688_);
v___x_2694_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___f_2688_, v_s_2689_, v___x_2693_, v___x_2692_);
v___x_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2691_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_box_uint64(v_javascriptHash_2690_);
v___x_2697_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2688_, v___x_2696_, v___x_2695_, v_s_2689_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object* v___f_2698_, lean_object* v_env_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2701_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2700_, v_env_2699_, v___f_2698_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object* v_inst_2703_, lean_object* v_wi_2704_){
_start:
{
lean_object* v_modifyEnv_2705_; lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; 
v_modifyEnv_2705_ = lean_ctor_get(v_inst_2703_, 1);
lean_inc(v_modifyEnv_2705_);
lean_dec_ref(v_inst_2703_);
v___f_2706_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___f_2707_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2707_, 0, v_wi_2704_);
lean_closure_set(v___f_2707_, 1, v___f_2706_);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2708_, 0, v___f_2707_);
v___x_2709_ = lean_apply_1(v_modifyEnv_2705_, v___f_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object* v_m_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_wi_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_Widget_addPanelWidgetLocal___redArg(v_inst_2712_, v_wi_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object* v_m_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_wi_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Widget_addPanelWidgetLocal(v_m_2715_, v_inst_2716_, v_inst_2717_, v_wi_2718_);
lean_dec_ref(v_inst_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object* v___f_2720_, uint64_t v_h_2721_, lean_object* v_st_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_box_uint64(v_h_2721_);
v___x_2724_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___f_2720_, v___x_2723_, v_st_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object* v___f_2725_, lean_object* v_h_2726_, lean_object* v_st_2727_){
_start:
{
uint64_t v_h_boxed_2728_; lean_object* v_res_2729_; 
v_h_boxed_2728_ = lean_unbox_uint64(v_h_2726_);
lean_dec_ref(v_h_2726_);
v_res_2729_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2725_, v_h_boxed_2728_, v_st_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object* v_inst_2730_, uint64_t v_h_2731_){
_start:
{
lean_object* v_modifyEnv_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; lean_object* v___x_2737_; 
v_modifyEnv_2732_ = lean_ctor_get(v_inst_2730_, 1);
lean_inc(v_modifyEnv_2732_);
lean_dec_ref(v_inst_2730_);
v___f_2733_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___x_2734_ = lean_box_uint64(v_h_2731_);
v___f_2735_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2735_, 0, v___f_2733_);
lean_closure_set(v___f_2735_, 1, v___x_2734_);
v___f_2736_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2736_, 0, v___f_2735_);
v___x_2737_ = lean_apply_1(v_modifyEnv_2732_, v___f_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object* v_inst_2738_, lean_object* v_h_2739_){
_start:
{
uint64_t v_h_boxed_2740_; lean_object* v_res_2741_; 
v_h_boxed_2740_ = lean_unbox_uint64(v_h_2739_);
lean_dec_ref(v_h_2739_);
v_res_2741_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2738_, v_h_boxed_2740_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget(lean_object* v_m_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, uint64_t v_h_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2744_, v_h_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object* v_m_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_h_2750_){
_start:
{
uint64_t v_h_boxed_2751_; lean_object* v_res_2752_; 
v_h_boxed_2751_ = lean_unbox_uint64(v_h_2750_);
lean_dec_ref(v_h_2750_);
v_res_2752_ = l_Lean_Widget_erasePanelWidget(v_m_2747_, v_inst_2748_, v_inst_2749_, v_h_boxed_2751_);
lean_dec_ref(v_inst_2748_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t v_hash_2753_, lean_object* v_props_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v_env_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v_val_2763_; lean_object* v___x_2766_; 
v___x_2758_ = lean_st_ref_get(v_a_2756_);
v_env_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc_ref(v_env_2759_);
lean_dec(v___x_2758_);
v___x_2760_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_2761_ = lean_st_ref_get(v___x_2760_);
v___x_2766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_2761_, v_hash_2753_);
lean_dec(v___x_2761_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v___x_2767_; lean_object* v_toEnvExtension_2768_; lean_object* v_asyncMode_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2767_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_2768_ = lean_ctor_get(v___x_2767_, 0);
v_asyncMode_2769_ = lean_ctor_get(v_toEnvExtension_2768_, 2);
v___x_2770_ = lean_box(1);
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2770_, v___x_2767_, v_env_2759_, v_asyncMode_2769_, v___x_2771_);
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_2772_, v_hash_2753_);
lean_dec(v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_dec_ref(v_props_2754_);
v___x_2774_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_2775_ = lean_uint64_to_nat(v_hash_2753_);
v___x_2776_ = l_Nat_reprFast(v___x_2775_);
v___x_2777_ = lean_string_append(v___x_2774_, v___x_2776_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_2779_ = lean_string_append(v___x_2777_, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
v___x_2781_ = l_Lean_MessageData_ofFormat(v___x_2780_);
v___x_2782_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v___x_2781_, v_a_2755_, v_a_2756_);
return v___x_2782_;
}
else
{
lean_object* v_val_2783_; lean_object* v_fst_2784_; 
v_val_2783_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v___x_2773_, 1);
v_fst_2784_ = lean_ctor_get(v_val_2783_, 0);
lean_inc(v_fst_2784_);
lean_dec(v_val_2783_);
v_val_2763_ = v_fst_2784_;
goto v___jp_2762_;
}
}
else
{
lean_object* v_val_2785_; lean_object* v_fst_2786_; 
lean_dec_ref(v_env_2759_);
v_val_2785_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2766_, 1);
v_fst_2786_ = lean_ctor_get(v_val_2785_, 0);
lean_inc(v_fst_2786_);
lean_dec(v_val_2785_);
v_val_2763_ = v_fst_2786_;
goto v___jp_2762_;
}
v___jp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2764_, 0, v_val_2763_);
lean_ctor_set(v___x_2764_, 1, v_props_2754_);
lean_ctor_set_uint64(v___x_2764_, sizeof(void*)*2, v_hash_2753_);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object* v_hash_2787_, lean_object* v_props_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
uint64_t v_hash_boxed_2792_; lean_object* v_res_2793_; 
v_hash_boxed_2792_ = lean_unbox_uint64(v_hash_2787_);
lean_dec_ref(v_hash_2787_);
v_res_2793_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_boxed_2792_, v_props_2788_, v_a_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object* v_t_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; lean_object* v_infoState_2798_; uint8_t v_enabled_2799_; 
v___x_2797_ = lean_st_ref_get(v___y_2795_);
v_infoState_2798_ = lean_ctor_get(v___x_2797_, 8);
lean_inc_ref(v_infoState_2798_);
lean_dec(v___x_2797_);
v_enabled_2799_ = lean_ctor_get_uint8(v_infoState_2798_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2798_);
if (v_enabled_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v_t_2794_);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; lean_object* v_infoState_2803_; lean_object* v_env_2804_; lean_object* v_nextMacroScope_2805_; lean_object* v_ngen_2806_; lean_object* v_auxDeclNGen_2807_; lean_object* v_traceState_2808_; lean_object* v_cache_2809_; lean_object* v_recordedDeps_2810_; lean_object* v_messages_2811_; lean_object* v_snapshotTasks_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2834_; 
v___x_2802_ = lean_st_ref_take(v___y_2795_);
v_infoState_2803_ = lean_ctor_get(v___x_2802_, 8);
v_env_2804_ = lean_ctor_get(v___x_2802_, 0);
v_nextMacroScope_2805_ = lean_ctor_get(v___x_2802_, 1);
v_ngen_2806_ = lean_ctor_get(v___x_2802_, 2);
v_auxDeclNGen_2807_ = lean_ctor_get(v___x_2802_, 3);
v_traceState_2808_ = lean_ctor_get(v___x_2802_, 4);
v_cache_2809_ = lean_ctor_get(v___x_2802_, 5);
v_recordedDeps_2810_ = lean_ctor_get(v___x_2802_, 6);
v_messages_2811_ = lean_ctor_get(v___x_2802_, 7);
v_snapshotTasks_2812_ = lean_ctor_get(v___x_2802_, 9);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2814_ = v___x_2802_;
v_isShared_2815_ = v_isSharedCheck_2834_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_snapshotTasks_2812_);
lean_inc(v_infoState_2803_);
lean_inc(v_messages_2811_);
lean_inc(v_recordedDeps_2810_);
lean_inc(v_cache_2809_);
lean_inc(v_traceState_2808_);
lean_inc(v_auxDeclNGen_2807_);
lean_inc(v_ngen_2806_);
lean_inc(v_nextMacroScope_2805_);
lean_inc(v_env_2804_);
lean_dec(v___x_2802_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2834_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint8_t v_enabled_2816_; lean_object* v_assignment_2817_; lean_object* v_lazyAssignment_2818_; lean_object* v_trees_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2833_; 
v_enabled_2816_ = lean_ctor_get_uint8(v_infoState_2803_, sizeof(void*)*3);
v_assignment_2817_ = lean_ctor_get(v_infoState_2803_, 0);
v_lazyAssignment_2818_ = lean_ctor_get(v_infoState_2803_, 1);
v_trees_2819_ = lean_ctor_get(v_infoState_2803_, 2);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_infoState_2803_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2821_ = v_infoState_2803_;
v_isShared_2822_ = v_isSharedCheck_2833_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_trees_2819_);
lean_inc(v_lazyAssignment_2818_);
lean_inc(v_assignment_2817_);
lean_dec(v_infoState_2803_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2833_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = l_Lean_PersistentArray_push___redArg(v_trees_2819_, v_t_2794_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 2, v___x_2824_);
v___x_2826_ = v___x_2821_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_assignment_2817_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_lazyAssignment_2818_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v___x_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*3, v_enabled_2816_);
v___x_2826_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 8, v___x_2826_);
v___x_2828_ = v___x_2814_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_env_2804_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_nextMacroScope_2805_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_ngen_2806_);
lean_ctor_set(v_reuseFailAlloc_2831_, 3, v_auxDeclNGen_2807_);
lean_ctor_set(v_reuseFailAlloc_2831_, 4, v_traceState_2808_);
lean_ctor_set(v_reuseFailAlloc_2831_, 5, v_cache_2809_);
lean_ctor_set(v_reuseFailAlloc_2831_, 6, v_recordedDeps_2810_);
lean_ctor_set(v_reuseFailAlloc_2831_, 7, v_messages_2811_);
lean_ctor_set(v_reuseFailAlloc_2831_, 8, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2831_, 9, v_snapshotTasks_2812_);
v___x_2828_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_st_ref_put(v___y_2795_, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2823_);
return v___x_2830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2835_, v___y_2836_);
lean_dec(v___y_2836_);
return v_res_2838_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_unsigned_to_nat(32u);
v___x_2840_ = lean_mk_empty_array_with_capacity(v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2842_ = ((size_t)5ULL);
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = lean_unsigned_to_nat(32u);
v___x_2845_ = lean_mk_empty_array_with_capacity(v___x_2844_);
v___x_2846_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0);
v___x_2847_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2845_);
lean_ctor_set(v___x_2847_, 2, v___x_2843_);
lean_ctor_set(v___x_2847_, 3, v___x_2843_);
lean_ctor_set_usize(v___x_2847_, 4, v___x_2842_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object* v_t_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v_infoState_2853_; uint8_t v_enabled_2854_; 
v___x_2852_ = lean_st_ref_get(v___y_2850_);
v_infoState_2853_ = lean_ctor_get(v___x_2852_, 8);
lean_inc_ref(v_infoState_2853_);
lean_dec(v___x_2852_);
v_enabled_2854_ = lean_ctor_get_uint8(v_infoState_2853_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2853_);
if (v_enabled_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec_ref(v_t_2848_);
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_t_2848_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v___x_2858_, v___y_2850_);
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object* v_t_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t v_hash_2865_, lean_object* v_props_2866_, lean_object* v_stx_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2865_, v_props_2866_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v_a_2872_);
lean_ctor_set(v___x_2873_, 1, v_stx_2867_);
v___x_2874_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
v___x_2875_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v___x_2874_, v_a_2868_, v_a_2869_);
return v___x_2875_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_stx_2867_);
v_a_2876_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2871_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2871_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object* v_hash_2884_, lean_object* v_props_2885_, lean_object* v_stx_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
uint64_t v_hash_boxed_2890_; lean_object* v_res_2891_; 
v_hash_boxed_2890_ = lean_unbox_uint64(v_hash_2884_);
lean_dec_ref(v_hash_2884_);
v_res_2891_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_boxed_2890_, v_props_2885_, v_stx_2886_, v_a_2887_, v_a_2888_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object* v_t_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2892_, v___y_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object* v_t_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object* v_x_2908_){
_start:
{
lean_object* v_name_2909_; lean_object* v_javascript_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2930_; 
v_name_2909_ = lean_ctor_get(v_x_2908_, 0);
v_javascript_2910_ = lean_ctor_get(v_x_2908_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_x_2908_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2912_ = v_x_2908_;
v_isShared_2913_ = v_isSharedCheck_2930_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_javascript_2910_);
lean_inc(v_name_2909_);
lean_dec(v_x_2908_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2930_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2914_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_2915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_name_2909_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v___x_2915_);
lean_ctor_set(v___x_2912_, 0, v___x_2914_);
v___x_2917_ = v___x_2912_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_2921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_javascript_2910_);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___x_2918_);
v___x_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v___x_2918_);
v___x_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2919_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_2927_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_2925_, v___x_2926_);
v___x_2928_ = l_Lean_Json_mkObj(v___x_2927_);
lean_dec(v___x_2927_);
return v___x_2928_;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = 1;
v___x_2939_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_2940_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2939_, v___x_2938_);
return v___x_2940_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_2942_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2);
v___x_2943_ = lean_string_append(v___x_2942_, v___x_2941_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = 1;
v___x_2947_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4));
v___x_2948_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2947_, v___x_2946_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5);
v___x_2950_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2951_ = lean_string_append(v___x_2950_, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2953_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6);
v___x_2954_ = lean_string_append(v___x_2953_, v___x_2952_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = 1;
v___x_2958_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8));
v___x_2959_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2958_, v___x_2957_);
return v___x_2959_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9);
v___x_2961_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_2962_ = lean_string_append(v___x_2961_, v___x_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_2964_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10);
v___x_2965_ = lean_string_append(v___x_2964_, v___x_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object* v_json_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
lean_inc(v_json_2966_);
v___x_2968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_2966_, v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_json_2966_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2978_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2978_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2973_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7);
v___x_2974_ = lean_string_append(v___x_2973_, v_a_2969_);
lean_dec(v_a_2969_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2974_);
v___x_2976_ = v___x_2971_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_a_2979_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2980_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_2981_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_2966_, v___x_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2979_);
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2984_ = v___x_2981_;
v_isShared_2985_ = v_isSharedCheck_2991_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2991_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2986_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11);
v___x_2987_ = lean_string_append(v___x_2986_, v_a_2982_);
lean_dec(v_a_2982_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2987_);
v___x_2989_ = v___x_2984_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3000_; 
v_a_2992_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2994_ = v___x_2981_;
v_isShared_2995_ = v_isSharedCheck_3000_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2981_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3000_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_a_2979_);
lean_ctor_set(v___x_2996_, 1, v_a_2992_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2996_);
v___x_2998_ = v___x_2994_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object* v_uwd_3003_){
_start:
{
lean_object* v_javascript_3004_; uint64_t v___x_3005_; lean_object* v___x_3006_; 
v_javascript_3004_ = lean_ctor_get(v_uwd_3003_, 1);
v___x_3005_ = lean_string_hash(v_javascript_3004_);
lean_inc_ref(v_javascript_3004_);
v___x_3006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3006_, 0, v_javascript_3004_);
lean_ctor_set_uint64(v___x_3006_, sizeof(void*)*1, v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object* v_uwd_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(v_uwd_3007_);
lean_dec_ref(v_uwd_3007_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object* v_____do__lift_3011_, lean_object* v_id_3012_, lean_object* v_inst_3013_, lean_object* v_inst_3014_, lean_object* v___x_3015_, lean_object* v_____do__lift_3016_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3018_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_3011_, v_____do__lift_3016_, v___x_3017_, v_id_3012_);
v___x_3019_ = l_Lean_ofExcept___redArg(v_inst_3013_, v_inst_3014_, v___x_3015_, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object* v_____do__lift_3020_, lean_object* v_id_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v___x_3024_, lean_object* v_____do__lift_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(v_____do__lift_3020_, v_id_3021_, v_inst_3022_, v_inst_3023_, v___x_3024_, v_____do__lift_3025_);
lean_dec_ref(v_____do__lift_3025_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object* v_inst_3027_, lean_object* v_id_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v___x_3031_, lean_object* v_toBind_3032_, lean_object* v_____do__lift_3033_){
_start:
{
lean_object* v_getOptions_3034_; lean_object* v___f_3035_; lean_object* v___x_3036_; 
v_getOptions_3034_ = lean_ctor_get(v_inst_3027_, 0);
lean_inc(v_getOptions_3034_);
lean_dec_ref(v_inst_3027_);
v___f_3035_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_3035_, 0, v_____do__lift_3033_);
lean_closure_set(v___f_3035_, 1, v_id_3028_);
lean_closure_set(v___f_3035_, 2, v_inst_3029_);
lean_closure_set(v___f_3035_, 3, v_inst_3030_);
lean_closure_set(v___f_3035_, 4, v___x_3031_);
v___x_3036_ = lean_apply_4(v_toBind_3032_, lean_box(0), lean_box(0), v_getOptions_3034_, v___f_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_id_3042_){
_start:
{
lean_object* v_toBind_3043_; lean_object* v_getEnv_3044_; lean_object* v___x_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; 
v_toBind_3043_ = lean_ctor_get(v_inst_3038_, 1);
lean_inc_n(v_toBind_3043_, 2);
v_getEnv_3044_ = lean_ctor_get(v_inst_3039_, 0);
lean_inc(v_getEnv_3044_);
lean_dec_ref(v_inst_3039_);
v___x_3045_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0));
v___f_3046_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3046_, 0, v_inst_3040_);
lean_closure_set(v___f_3046_, 1, v_id_3042_);
lean_closure_set(v___f_3046_, 2, v_inst_3038_);
lean_closure_set(v___f_3046_, 3, v_inst_3041_);
lean_closure_set(v___f_3046_, 4, v___x_3045_);
lean_closure_set(v___f_3046_, 5, v_toBind_3043_);
v___x_3047_ = lean_apply_4(v_toBind_3043_, lean_box(0), lean_box(0), v_getEnv_3044_, v___f_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object* v_m_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_id_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(v_inst_3049_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_id_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object* v_text_3055_, lean_object* v_hoverLine_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 9)
{
lean_object* v_i_3060_; lean_object* v___x_3061_; 
v_i_3060_ = lean_ctor_get(v_x_3058_, 0);
v___x_3061_ = l_Lean_Elab_Info_pos_x3f(v_x_3058_);
if (lean_obj_tag(v___x_3061_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3063_; 
v_val_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_val_3062_);
lean_dec_ref_known(v___x_3061_, 1);
v___x_3063_ = l_Lean_Elab_Info_tailPos_x3f(v_x_3058_);
if (lean_obj_tag(v___x_3063_) == 1)
{
lean_object* v_val_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3079_; 
v_val_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3079_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_val_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3079_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v_line_3069_; uint8_t v___x_3070_; 
lean_inc_ref(v_text_3055_);
v___x_3068_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3055_, v_val_3062_);
lean_dec(v_val_3062_);
v_line_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_line_3069_);
lean_dec_ref(v___x_3068_);
v___x_3070_ = lean_nat_dec_le(v_line_3069_, v_hoverLine_3056_);
lean_dec(v_line_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
lean_del_object(v___x_3066_);
lean_dec(v_val_3064_);
lean_dec_ref(v_text_3055_);
v___x_3071_ = lean_box(0);
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v_line_3073_; uint8_t v___x_3074_; 
v___x_3072_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3055_, v_val_3064_);
lean_dec(v_val_3064_);
v_line_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_line_3073_);
lean_dec_ref(v___x_3072_);
v___x_3074_ = lean_nat_dec_le(v_hoverLine_3056_, v_line_3073_);
lean_dec(v_line_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; 
lean_del_object(v___x_3066_);
v___x_3075_ = lean_box(0);
return v___x_3075_;
}
else
{
lean_object* v___x_3077_; 
lean_inc_ref(v_i_3060_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_i_3060_);
v___x_3077_ = v___x_3066_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_i_3060_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
else
{
lean_object* v___x_3080_; 
lean_dec(v___x_3063_);
lean_dec(v_val_3062_);
lean_dec_ref(v_text_3055_);
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
}
else
{
lean_object* v___x_3081_; 
lean_dec(v___x_3061_);
lean_dec_ref(v_text_3055_);
v___x_3081_ = lean_box(0);
return v___x_3081_;
}
}
else
{
lean_object* v___x_3082_; 
lean_dec_ref(v_text_3055_);
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object* v_text_3083_, lean_object* v_hoverLine_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Widget_widgetInfosAt_x3f___lam__0(v_text_3083_, v_hoverLine_3084_, v_x_3085_, v_x_3086_, v_x_3087_);
lean_dec_ref(v_x_3087_);
lean_dec_ref(v_x_3086_);
lean_dec_ref(v_x_3085_);
lean_dec(v_hoverLine_3084_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object* v_text_3089_, lean_object* v_t_3090_, lean_object* v_hoverLine_3091_){
_start:
{
lean_object* v___f_3092_; lean_object* v___x_3093_; 
v___f_3092_ = lean_alloc_closure((void*)(l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_3092_, 0, v_text_3089_);
lean_closure_set(v___f_3092_, 1, v_hoverLine_3091_);
v___x_3093_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3092_, v_t_3090_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object* v_j_3094_, lean_object* v_k_3095_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = l_Lean_Json_getObjValD(v_j_3094_, v_k_3095_);
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object* v_j_3098_, lean_object* v_k_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_j_3098_, v_k_3099_);
lean_dec_ref(v_k_3099_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object* v_x_3103_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 0)
{
lean_object* v___x_3104_; 
v___x_3104_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0));
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_x_3103_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object* v_j_3107_, lean_object* v_k_3108_){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = l_Lean_Json_getObjValD(v_j_3107_, v_k_3108_);
v___x_3110_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object* v_j_3111_, lean_object* v_k_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_j_3111_, v_k_3112_);
lean_dec_ref(v_k_3112_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object* v_json_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v_a_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v_a_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v_a_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v_a_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3141_; 
v___x_3119_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc_n(v_json_3118_, 4);
v___x_3120_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3118_, v___x_3119_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3120_);
v___x_3122_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3123_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3118_, v___x_3122_);
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v___x_3125_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3126_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3118_, v___x_3125_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3129_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3118_, v___x_3128_);
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3132_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3118_, v___x_3131_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3141_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3141_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3137_, 0, v_a_3121_);
lean_ctor_set(v___x_3137_, 1, v_a_3124_);
lean_ctor_set(v___x_3137_, 2, v_a_3127_);
lean_ctor_set(v___x_3137_, 3, v_a_3130_);
lean_ctor_set(v___x_3137_, 4, v_a_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(lean_object* v_k_3144_, lean_object* v_x_3145_){
_start:
{
if (lean_obj_tag(v_x_3145_) == 0)
{
lean_object* v___x_3146_; 
lean_dec_ref(v_k_3144_);
v___x_3146_ = lean_box(0);
return v___x_3146_;
}
else
{
lean_object* v_val_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_val_3147_ = lean_ctor_get(v_x_3145_, 0);
lean_inc(v_val_3147_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_k_3144_);
lean_ctor_set(v___x_3148_, 1, v_val_3147_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0___boxed(lean_object* v_k_3151_, lean_object* v_x_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v_k_3151_, v_x_3152_);
lean_dec(v_x_3152_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(lean_object* v_x_3154_){
_start:
{
lean_object* v_id_3155_; lean_object* v_javascriptHash_3156_; lean_object* v_props_3157_; lean_object* v_range_x3f_3158_; lean_object* v_name_x3f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_id_3155_ = lean_ctor_get(v_x_3154_, 0);
v_javascriptHash_3156_ = lean_ctor_get(v_x_3154_, 1);
v_props_3157_ = lean_ctor_get(v_x_3154_, 2);
v_range_x3f_3158_ = lean_ctor_get(v_x_3154_, 3);
v_name_x3f_3159_ = lean_ctor_get(v_x_3154_, 4);
v___x_3160_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_id_3155_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v_id_3155_);
v___x_3162_ = lean_box(0);
v___x_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_javascriptHash_3156_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v_javascriptHash_3156_);
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3162_);
v___x_3167_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_props_3157_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v_props_3157_);
v___x_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3162_);
v___x_3170_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3171_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v___x_3170_, v_range_x3f_3158_);
v___x_3172_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3173_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v___x_3172_, v_name_x3f_3159_);
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3162_);
v___x_3175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3171_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3169_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3166_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3163_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3180_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3178_, v___x_3179_);
v___x_3181_ = l_Lean_Json_mkObj(v___x_3180_);
lean_dec(v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39____boxed(lean_object* v_x_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(v_x_3182_);
lean_dec_ref(v_x_3182_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_toWidgetInstance_3188_; lean_object* v_range_x3f_3189_; lean_object* v_name_x3f_3190_; lean_object* v_id_3191_; uint64_t v_javascriptHash_3192_; lean_object* v_props_3193_; lean_object* v___x_3194_; lean_object* v_fst_3195_; lean_object* v_snd_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3236_; 
v_toWidgetInstance_3188_ = lean_ctor_get(v_a_3186_, 0);
lean_inc_ref(v_toWidgetInstance_3188_);
v_range_x3f_3189_ = lean_ctor_get(v_a_3186_, 1);
lean_inc(v_range_x3f_3189_);
v_name_x3f_3190_ = lean_ctor_get(v_a_3186_, 2);
lean_inc(v_name_x3f_3190_);
lean_dec_ref(v_a_3186_);
v_id_3191_ = lean_ctor_get(v_toWidgetInstance_3188_, 0);
lean_inc(v_id_3191_);
v_javascriptHash_3192_ = lean_ctor_get_uint64(v_toWidgetInstance_3188_, sizeof(void*)*2);
v_props_3193_ = lean_ctor_get(v_toWidgetInstance_3188_, 1);
lean_inc_ref(v_props_3193_);
lean_dec_ref(v_toWidgetInstance_3188_);
v___x_3194_ = lean_apply_1(v_props_3193_, v_a_3187_);
v_fst_3195_ = lean_ctor_get(v___x_3194_, 0);
v_snd_3196_ = lean_ctor_get(v___x_3194_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3198_ = v___x_3194_;
v_isShared_3199_ = v_isSharedCheck_3236_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_snd_3196_);
lean_inc(v_fst_3195_);
lean_dec(v___x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3236_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___y_3206_; lean_object* v_fst_3207_; lean_object* v_snd_3208_; lean_object* v_fst_3215_; 
v___x_3200_ = 1;
v___x_3201_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3191_, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
v___x_3203_ = lean_uint64_to_nat(v_javascriptHash_3192_);
v___x_3204_ = l_Lean_bignumToJson(v___x_3203_);
if (lean_obj_tag(v_range_x3f_3189_) == 0)
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_box(0);
v_fst_3215_ = v___x_3226_;
goto v___jp_3214_;
}
else
{
lean_object* v_val_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3235_; 
v_val_3227_ = lean_ctor_get(v_range_x3f_3189_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_range_x3f_3189_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3229_ = v_range_x3f_3189_;
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_val_3227_);
lean_dec(v_range_x3f_3189_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_3227_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3231_);
v___x_3233_ = v___x_3229_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
v_fst_3215_ = v___x_3233_;
goto v___jp_3214_;
}
}
}
v___jp_3205_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3202_);
lean_ctor_set(v___x_3209_, 1, v___x_3204_);
lean_ctor_set(v___x_3209_, 2, v_fst_3195_);
lean_ctor_set(v___x_3209_, 3, v___y_3206_);
lean_ctor_set(v___x_3209_, 4, v_fst_3207_);
v___x_3210_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(v___x_3209_);
lean_dec_ref_known(v___x_3209_, 5);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 1, v_snd_3208_);
lean_ctor_set(v___x_3198_, 0, v___x_3210_);
v___x_3212_ = v___x_3198_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_snd_3208_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
v___jp_3214_:
{
if (lean_obj_tag(v_name_x3f_3190_) == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_box(0);
v___y_3206_ = v_fst_3215_;
v_fst_3207_ = v___x_3216_;
v_snd_3208_ = v_snd_3196_;
goto v___jp_3205_;
}
else
{
lean_object* v_val_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3225_; 
v_val_3217_ = lean_ctor_get(v_name_x3f_3190_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_name_x3f_3190_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3219_ = v_name_x3f_3190_;
v_isShared_3220_ = v_isSharedCheck_3225_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_val_3217_);
lean_dec(v_name_x3f_3190_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3225_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_val_3217_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3221_);
v___x_3223_ = v___x_3219_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
v___y_3206_ = v_fst_3215_;
v_fst_3207_ = v___x_3223_;
v_snd_3208_ = v_snd_3196_;
goto v___jp_3205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_props_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_props_3237_);
lean_ctor_set(v___x_3239_, 1, v___y_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(v_j_3240_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v_id_3251_; lean_object* v_javascriptHash_3252_; lean_object* v_props_3253_; lean_object* v_range_x3f_3254_; lean_object* v_name_x3f_3255_; lean_object* v___x_3256_; 
v_a_3250_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3241_, 1);
v_id_3251_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_id_3251_);
v_javascriptHash_3252_ = lean_ctor_get(v_a_3250_, 1);
lean_inc(v_javascriptHash_3252_);
v_props_3253_ = lean_ctor_get(v_a_3250_, 2);
lean_inc(v_props_3253_);
v_range_x3f_3254_ = lean_ctor_get(v_a_3250_, 3);
lean_inc(v_range_x3f_3254_);
v_name_x3f_3255_ = lean_ctor_get(v_a_3250_, 4);
lean_inc(v_name_x3f_3255_);
lean_dec(v_a_3250_);
v___x_3256_ = l_Lean_Name_fromJson_x3f(v_id_3251_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v_name_x3f_3255_);
lean_dec(v_range_x3f_3254_);
lean_dec(v_props_3253_);
lean_dec(v_javascriptHash_3252_);
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3266_ = l_Lean_UInt64_fromJson_x3f(v_javascriptHash_3252_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_a_3265_);
lean_dec(v_name_x3f_3255_);
lean_dec(v_range_x3f_3254_);
lean_dec(v_props_3253_);
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3329_; 
v_a_3275_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3277_ = v___x_3266_;
v_isShared_3278_ = v_isSharedCheck_3329_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3266_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3329_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___f_3279_; lean_object* v___y_3281_; lean_object* v_____do__lift_3282_; lean_object* v_____do__lift_3290_; 
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_), 2, 1);
lean_closure_set(v___f_3279_, 0, v_props_3253_);
if (lean_obj_tag(v_range_x3f_3254_) == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_box(0);
v_____do__lift_3290_ = v___x_3310_;
goto v___jp_3289_;
}
else
{
lean_object* v_val_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3328_; 
v_val_3311_ = lean_ctor_get(v_range_x3f_3254_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_range_x3f_3254_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3313_ = v_range_x3f_3254_;
v_isShared_3314_ = v_isSharedCheck_3328_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_val_3311_);
lean_dec(v_range_x3f_3254_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3328_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_3311_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_del_object(v___x_3313_);
lean_dec_ref(v___f_3279_);
lean_del_object(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec(v_a_3265_);
lean_dec(v_name_x3f_3255_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; 
v_a_3324_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3315_, 1);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v_a_3324_);
v___x_3326_ = v___x_3313_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
v_____do__lift_3290_ = v___x_3326_;
goto v___jp_3289_;
}
}
}
}
v___jp_3280_:
{
lean_object* v___x_3283_; uint64_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3283_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3283_, 0, v_a_3265_);
lean_ctor_set(v___x_3283_, 1, v___f_3279_);
v___x_3284_ = lean_unbox_uint64(v_a_3275_);
lean_dec(v_a_3275_);
lean_ctor_set_uint64(v___x_3283_, sizeof(void*)*2, v___x_3284_);
v___x_3285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___y_3281_);
lean_ctor_set(v___x_3285_, 2, v_____do__lift_3282_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3285_);
v___x_3287_ = v___x_3277_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
v___jp_3289_:
{
if (lean_obj_tag(v_name_x3f_3255_) == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_box(0);
v___y_3281_ = v_____do__lift_3290_;
v_____do__lift_3282_ = v___x_3291_;
goto v___jp_3280_;
}
else
{
lean_object* v_val_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3309_; 
v_val_3292_ = lean_ctor_get(v_name_x3f_3255_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v_name_x3f_3255_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3294_ = v_name_x3f_3255_;
v_isShared_3295_ = v_isSharedCheck_3309_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_val_3292_);
lean_dec(v_name_x3f_3255_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3309_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Json_getStr_x3f(v_val_3292_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_del_object(v___x_3294_);
lean_dec(v_____do__lift_3290_);
lean_dec_ref(v___f_3279_);
lean_del_object(v___x_3277_);
lean_dec(v_a_3275_);
lean_dec(v_a_3265_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; 
v_a_3305_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3296_, 1);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v_a_3305_);
v___x_3307_ = v___x_3294_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
v___y_3281_ = v_____do__lift_3290_;
v_____do__lift_3282_ = v___x_3307_;
goto v___jp_3280_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object* v_j_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3333_, v_a_3334_);
lean_dec_ref(v_a_3334_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object* v_json_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
v___x_3344_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3345_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3343_, v___x_3344_);
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(lean_object* v_x_3356_){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3357_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v_x_3356_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3358_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___x_3359_);
v___x_3362_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3363_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3361_, v___x_3362_);
v___x_3364_ = l_Lean_Json_mkObj(v___x_3363_);
lean_dec(v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t v_sz_3367_, size_t v_i_3368_, lean_object* v_bs_3369_){
_start:
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_usize_dec_lt(v_i_3368_, v_sz_3367_);
if (v___x_3370_ == 0)
{
return v_bs_3369_;
}
else
{
lean_object* v_v_3371_; lean_object* v___x_3372_; lean_object* v_bs_x27_3373_; size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v_v_3371_ = lean_array_uget(v_bs_3369_, v_i_3368_);
v___x_3372_ = lean_unsigned_to_nat(0u);
v_bs_x27_3373_ = lean_array_uset(v_bs_3369_, v_i_3368_, v___x_3372_);
v___x_3374_ = ((size_t)1ULL);
v___x_3375_ = lean_usize_add(v_i_3368_, v___x_3374_);
v___x_3376_ = lean_array_uset(v_bs_x27_3373_, v_i_3368_, v_v_3371_);
v_i_3368_ = v___x_3375_;
v_bs_3369_ = v___x_3376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object* v_sz_3378_, lean_object* v_i_3379_, lean_object* v_bs_3380_){
_start:
{
size_t v_sz_boxed_3381_; size_t v_i_boxed_3382_; lean_object* v_res_3383_; 
v_sz_boxed_3381_ = lean_unbox_usize(v_sz_3378_);
lean_dec(v_sz_3378_);
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_res_3383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_boxed_3381_, v_i_boxed_3382_, v_bs_3380_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object* v_a_3384_){
_start:
{
size_t v_sz_3385_; size_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_sz_3385_ = lean_array_size(v_a_3384_);
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3385_, v___x_3386_, v_a_3384_);
v___x_3388_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t v_sz_3389_, size_t v_i_3390_, lean_object* v_bs_3391_, lean_object* v___y_3392_){
_start:
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_usize_dec_lt(v_i_3390_, v_sz_3389_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_bs_3391_);
lean_ctor_set(v___x_3394_, 1, v___y_3392_);
return v___x_3394_;
}
else
{
lean_object* v_v_3395_; lean_object* v___x_3396_; lean_object* v_fst_3397_; lean_object* v_snd_3398_; lean_object* v___x_3399_; lean_object* v_bs_x27_3400_; size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; 
v_v_3395_ = lean_array_uget_borrowed(v_bs_3391_, v_i_3390_);
lean_inc(v_v_3395_);
v___x_3396_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3395_, v___y_3392_);
v_fst_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_fst_3397_);
v_snd_3398_ = lean_ctor_get(v___x_3396_, 1);
lean_inc(v_snd_3398_);
lean_dec_ref(v___x_3396_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v_bs_x27_3400_ = lean_array_uset(v_bs_3391_, v_i_3390_, v___x_3399_);
v___x_3401_ = ((size_t)1ULL);
v___x_3402_ = lean_usize_add(v_i_3390_, v___x_3401_);
v___x_3403_ = lean_array_uset(v_bs_x27_3400_, v_i_3390_, v_fst_3397_);
v_i_3390_ = v___x_3402_;
v_bs_3391_ = v___x_3403_;
v___y_3392_ = v_snd_3398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object* v_sz_3405_, lean_object* v_i_3406_, lean_object* v_bs_3407_, lean_object* v___y_3408_){
_start:
{
size_t v_sz_boxed_3409_; size_t v_i_boxed_3410_; lean_object* v_res_3411_; 
v_sz_boxed_3409_ = lean_unbox_usize(v_sz_3405_);
lean_dec(v_sz_3405_);
v_i_boxed_3410_ = lean_unbox_usize(v_i_3406_);
lean_dec(v_i_3406_);
v_res_3411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_boxed_3409_, v_i_boxed_3410_, v_bs_3407_, v___y_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
size_t v_sz_3414_; size_t v___x_3415_; lean_object* v___x_3416_; lean_object* v_fst_3417_; lean_object* v_snd_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3427_; 
v_sz_3414_ = lean_array_size(v_a_3412_);
v___x_3415_ = ((size_t)0ULL);
v___x_3416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3414_, v___x_3415_, v_a_3412_, v_a_3413_);
v_fst_3417_ = lean_ctor_get(v___x_3416_, 0);
v_snd_3418_ = lean_ctor_get(v___x_3416_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3420_ = v___x_3416_;
v_isShared_3421_ = v_isSharedCheck_3427_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_snd_3418_);
lean_inc(v_fst_3417_);
lean_dec(v___x_3416_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3427_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3422_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_fst_3417_);
v___x_3423_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(v___x_3422_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3423_);
v___x_3425_ = v___x_3420_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_snd_3418_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t v_sz_3428_, size_t v_i_3429_, lean_object* v_bs_3430_){
_start:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_usize_dec_lt(v_i_3429_, v_sz_3428_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3432_, 0, v_bs_3430_);
return v___x_3432_;
}
else
{
lean_object* v_v_3433_; lean_object* v___x_3434_; 
v_v_3433_ = lean_array_uget_borrowed(v_bs_3430_, v_i_3429_);
lean_inc(v_v_3433_);
v___x_3434_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3433_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_bs_3430_);
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v_bs_x27_3445_; size_t v___x_3446_; size_t v___x_3447_; lean_object* v___x_3448_; 
v_a_3443_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3444_ = lean_unsigned_to_nat(0u);
v_bs_x27_3445_ = lean_array_uset(v_bs_3430_, v_i_3429_, v___x_3444_);
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_add(v_i_3429_, v___x_3446_);
v___x_3448_ = lean_array_uset(v_bs_x27_3445_, v_i_3429_, v_a_3443_);
v_i_3429_ = v___x_3447_;
v_bs_3430_ = v___x_3448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object* v_sz_3450_, lean_object* v_i_3451_, lean_object* v_bs_3452_){
_start:
{
size_t v_sz_boxed_3453_; size_t v_i_boxed_3454_; lean_object* v_res_3455_; 
v_sz_boxed_3453_ = lean_unbox_usize(v_sz_3450_);
lean_dec(v_sz_3450_);
v_i_boxed_3454_ = lean_unbox_usize(v_i_3451_);
lean_dec(v_i_3451_);
v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_boxed_3453_, v_i_boxed_3454_, v_bs_3452_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t v_sz_3456_, size_t v_i_3457_, lean_object* v_bs_3458_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_usize_dec_lt(v_i_3457_, v_sz_3456_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_bs_3458_);
return v___x_3460_;
}
else
{
lean_object* v_v_3461_; lean_object* v___x_3462_; lean_object* v_bs_x27_3463_; size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v_v_3461_ = lean_array_uget(v_bs_3458_, v_i_3457_);
v___x_3462_ = lean_unsigned_to_nat(0u);
v_bs_x27_3463_ = lean_array_uset(v_bs_3458_, v_i_3457_, v___x_3462_);
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3457_, v___x_3464_);
v___x_3466_ = lean_array_uset(v_bs_x27_3463_, v_i_3457_, v_v_3461_);
v_i_3457_ = v___x_3465_;
v_bs_3458_ = v___x_3466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_bs_3470_){
_start:
{
size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_3471_, v_i_boxed_3472_, v_bs_3470_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object* v_x_3475_){
_start:
{
if (lean_obj_tag(v_x_3475_) == 4)
{
lean_object* v_elems_3476_; size_t v_sz_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v_elems_3476_ = lean_ctor_get(v_x_3475_, 0);
lean_inc_ref(v_elems_3476_);
lean_dec_ref_known(v_x_3475_, 1);
v_sz_3477_ = lean_array_size(v_elems_3476_);
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3477_, v___x_3478_, v_elems_3476_);
return v___x_3479_;
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3480_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0));
v___x_3481_ = lean_unsigned_to_nat(80u);
v___x_3482_ = l_Lean_Json_pretty(v_x_3475_, v___x_3481_);
v___x_3483_ = lean_string_append(v___x_3480_, v___x_3482_);
lean_dec_ref(v___x_3482_);
v___x_3484_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v___x_3485_ = lean_string_append(v___x_3483_, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_j_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(v_j_3487_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3499_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_a_3498_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
else
{
lean_object* v_a_3508_; size_t v_sz_3509_; size_t v___x_3510_; lean_object* v___x_3511_; 
v_a_3508_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3499_, 1);
v_sz_3509_ = lean_array_size(v_a_3508_);
v___x_3510_ = ((size_t)0ULL);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3509_, v___x_3510_, v_a_3508_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3511_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3511_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object* v_j_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_j_3528_, v_a_3529_);
lean_dec_ref(v_a_3529_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t v_sz_3531_, size_t v_i_3532_, lean_object* v_bs_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3531_, v_i_3532_, v_bs_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object* v_sz_3536_, lean_object* v_i_3537_, lean_object* v_bs_3538_, lean_object* v___y_3539_){
_start:
{
size_t v_sz_boxed_3540_; size_t v_i_boxed_3541_; lean_object* v_res_3542_; 
v_sz_boxed_3540_ = lean_unbox_usize(v_sz_3536_);
lean_dec(v_sz_3536_);
v_i_boxed_3541_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_boxed_3540_, v_i_boxed_3541_, v_bs_3538_, v___y_3539_);
lean_dec_ref(v___y_3539_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object* v_x_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
if (lean_obj_tag(v_x_3549_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_a_3555_ = lean_ctor_get(v_x_3549_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v_x_3549_, 1);
v___x_3556_ = l_Lean_stringToMessageData(v_a_3555_);
v___x_3557_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_3556_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
return v___x_3557_;
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v_a_3558_ = lean_ctor_get(v_x_3549_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_x_3549_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v_x_3549_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v_x_3549_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 0);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object* v_x_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object* v_id_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; lean_object* v_env_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3579_ = lean_st_ref_get(v___y_3577_);
v_env_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc_ref(v_env_3580_);
lean_dec(v___x_3579_);
v___x_3581_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3576_);
v___x_3582_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3583_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3580_, v___x_3581_, v___x_3582_, v_id_3573_);
lean_dec_ref(v___x_3581_);
v___x_3584_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v___x_3583_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object* v_id_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object* v___x_3592_, size_t v_sz_3593_, size_t v_i_3594_, lean_object* v_bs_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
uint8_t v___x_3601_; 
v___x_3601_ = lean_usize_dec_lt(v_i_3594_, v_sz_3593_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
lean_dec_ref(v___x_3592_);
v___x_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3602_, 0, v_bs_3595_);
return v___x_3602_;
}
else
{
lean_object* v_v_3603_; lean_object* v_id_3604_; lean_object* v___x_3605_; lean_object* v_bs_x27_3606_; lean_object* v_a_3608_; uint8_t v___x_3617_; lean_object* v___x_3618_; 
v_v_3603_ = lean_array_uget(v_bs_3595_, v_i_3594_);
v_id_3604_ = lean_ctor_get(v_v_3603_, 0);
v___x_3605_ = lean_unsigned_to_nat(0u);
v_bs_x27_3606_ = lean_array_uset(v_bs_3595_, v_i_3594_, v___x_3605_);
v___x_3617_ = 0;
lean_inc(v_id_3604_);
lean_inc_ref(v___x_3592_);
v___x_3618_ = l_Lean_Environment_find_x3f(v___x_3592_, v_id_3604_, v___x_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
goto v___jp_3615_;
}
else
{
lean_object* v_val_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3640_; 
v_val_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3640_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_val_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3640_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3623_ = l_Lean_ConstantInfo_type(v_val_3619_);
lean_dec(v_val_3619_);
v___x_3624_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3625_ = l_Lean_Expr_isConstOf(v___x_3623_, v___x_3624_);
lean_dec_ref(v___x_3623_);
if (v___x_3625_ == 0)
{
lean_del_object(v___x_3621_);
goto v___jp_3615_;
}
else
{
lean_object* v___x_3626_; 
lean_inc(v_id_3604_);
v___x_3626_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3604_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v_name_3628_; lean_object* v___x_3630_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v_name_3628_ = lean_ctor_get(v_a_3627_, 0);
lean_inc_ref(v_name_3628_);
lean_dec(v_a_3627_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v_name_3628_);
v___x_3630_ = v___x_3621_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_name_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
v_a_3608_ = v___x_3630_;
goto v___jp_3607_;
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_del_object(v___x_3621_);
lean_dec_ref(v_bs_x27_3606_);
lean_dec(v_v_3603_);
lean_dec_ref(v___x_3592_);
v_a_3632_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3626_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3626_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
}
v___jp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; lean_object* v___x_3613_; 
v___x_3609_ = lean_box(0);
v___x_3610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3610_, 0, v_v_3603_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
lean_ctor_set(v___x_3610_, 2, v_a_3608_);
v___x_3611_ = ((size_t)1ULL);
v___x_3612_ = lean_usize_add(v_i_3594_, v___x_3611_);
v___x_3613_ = lean_array_uset(v_bs_x27_3606_, v_i_3594_, v___x_3610_);
v_i_3594_ = v___x_3612_;
v_bs_3595_ = v___x_3613_;
goto _start;
}
v___jp_3615_:
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_box(0);
v_a_3608_ = v___x_3616_;
goto v___jp_3607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object* v___x_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_bs_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
size_t v_sz_boxed_3650_; size_t v_i_boxed_3651_; lean_object* v_res_3652_; 
v_sz_boxed_3650_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3651_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3641_, v_sz_boxed_3650_, v_i_boxed_3651_, v_bs_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object* v___x_3653_, lean_object* v___x_3654_, size_t v_sz_3655_, size_t v_i_3656_, lean_object* v_bs_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
uint8_t v___x_3663_; 
v___x_3663_ = lean_usize_dec_lt(v_i_3656_, v_sz_3655_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_dec_ref(v___x_3654_);
lean_dec_ref(v___x_3653_);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v_bs_3657_);
return v___x_3664_;
}
else
{
lean_object* v_v_3665_; lean_object* v_toWidgetInstance_3666_; lean_object* v_stx_3667_; lean_object* v_id_3668_; lean_object* v___x_3669_; lean_object* v_bs_x27_3670_; lean_object* v___y_3672_; lean_object* v___y_3673_; uint8_t v___x_3679_; lean_object* v_a_3681_; lean_object* v___x_3695_; 
v_v_3665_ = lean_array_uget_borrowed(v_bs_3657_, v_i_3656_);
v_toWidgetInstance_3666_ = lean_ctor_get(v_v_3665_, 0);
lean_inc_ref(v_toWidgetInstance_3666_);
v_stx_3667_ = lean_ctor_get(v_v_3665_, 1);
lean_inc(v_stx_3667_);
v_id_3668_ = lean_ctor_get(v_toWidgetInstance_3666_, 0);
v___x_3669_ = lean_unsigned_to_nat(0u);
v_bs_x27_3670_ = lean_array_uset(v_bs_3657_, v_i_3656_, v___x_3669_);
v___x_3679_ = 0;
lean_inc(v_id_3668_);
lean_inc_ref(v___x_3654_);
v___x_3695_ = l_Lean_Environment_find_x3f(v___x_3654_, v_id_3668_, v___x_3679_);
if (lean_obj_tag(v___x_3695_) == 0)
{
goto v___jp_3693_;
}
else
{
lean_object* v_val_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3717_; 
v_val_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3717_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_val_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3717_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3700_ = l_Lean_ConstantInfo_type(v_val_3696_);
lean_dec(v_val_3696_);
v___x_3701_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3702_ = l_Lean_Expr_isConstOf(v___x_3700_, v___x_3701_);
lean_dec_ref(v___x_3700_);
if (v___x_3702_ == 0)
{
lean_del_object(v___x_3698_);
goto v___jp_3693_;
}
else
{
lean_object* v___x_3703_; 
lean_inc(v_id_3668_);
v___x_3703_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3668_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v_name_3705_; lean_object* v___x_3707_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3703_, 1);
v_name_3705_ = lean_ctor_get(v_a_3704_, 0);
lean_inc_ref(v_name_3705_);
lean_dec(v_a_3704_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v_name_3705_);
v___x_3707_ = v___x_3698_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_name_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
v_a_3681_ = v___x_3707_;
goto v___jp_3680_;
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_del_object(v___x_3698_);
lean_dec_ref(v_bs_x27_3670_);
lean_dec(v_stx_3667_);
lean_dec_ref(v_toWidgetInstance_3666_);
lean_dec_ref(v___x_3654_);
lean_dec_ref(v___x_3653_);
v_a_3709_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3703_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3703_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
}
v___jp_3671_:
{
lean_object* v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3674_, 0, v_toWidgetInstance_3666_);
lean_ctor_set(v___x_3674_, 1, v___y_3673_);
lean_ctor_set(v___x_3674_, 2, v___y_3672_);
v___x_3675_ = ((size_t)1ULL);
v___x_3676_ = lean_usize_add(v_i_3656_, v___x_3675_);
v___x_3677_ = lean_array_uset(v_bs_x27_3670_, v_i_3656_, v___x_3674_);
v_i_3656_ = v___x_3676_;
v_bs_3657_ = v___x_3677_;
goto _start;
}
v___jp_3680_:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Syntax_getRange_x3f(v_stx_3667_, v___x_3679_);
lean_dec(v_stx_3667_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_box(0);
v___y_3672_ = v_a_3681_;
v___y_3673_ = v___x_3683_;
goto v___jp_3671_;
}
else
{
lean_object* v_val_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3692_; 
v_val_3684_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3686_ = v___x_3682_;
v_isShared_3687_ = v_isSharedCheck_3692_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_val_3684_);
lean_dec(v___x_3682_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3692_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
lean_inc_ref(v___x_3653_);
v___x_3688_ = l_Lean_Syntax_Range_toLspRange(v___x_3653_, v_val_3684_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3688_);
v___x_3690_ = v___x_3686_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
v___y_3672_ = v_a_3681_;
v___y_3673_ = v___x_3690_;
goto v___jp_3671_;
}
}
}
}
v___jp_3693_:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_box(0);
v_a_3681_ = v___x_3694_;
goto v___jp_3680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object* v___x_3718_, lean_object* v___x_3719_, lean_object* v_sz_3720_, lean_object* v_i_3721_, lean_object* v_bs_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
size_t v_sz_boxed_3728_; size_t v_i_boxed_3729_; lean_object* v_res_3730_; 
v_sz_boxed_3728_ = lean_unbox_usize(v_sz_3720_);
lean_dec(v_sz_3720_);
v_i_boxed_3729_ = lean_unbox_usize(v_i_3721_);
lean_dec(v_i_3721_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3718_, v___x_3719_, v_sz_boxed_3728_, v_i_boxed_3729_, v_bs_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object* v_pos_3731_, lean_object* v_text_3732_, lean_object* v_val_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; lean_object* v_env_3740_; lean_object* v___x_3741_; 
v___x_3739_ = lean_st_ref_get(v___y_3737_);
v_env_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc_ref(v_env_3740_);
lean_dec(v___x_3739_);
v___x_3741_ = l_Lean_Widget_evalPanelWidgets(v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; size_t v_sz_3743_; size_t v___x_3744_; lean_object* v___x_3745_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
lean_dec_ref_known(v___x_3741_, 1);
v_sz_3743_ = lean_array_size(v_a_3742_);
v___x_3744_ = ((size_t)0ULL);
lean_inc_ref(v_env_3740_);
v___x_3745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v_env_3740_, v_sz_3743_, v___x_3744_, v_a_3742_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v_line_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; size_t v_sz_3750_; lean_object* v___x_3751_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v_line_3747_ = lean_ctor_get(v_pos_3731_, 0);
lean_inc(v_line_3747_);
lean_dec_ref(v_pos_3731_);
lean_inc_ref(v_text_3732_);
v___x_3748_ = l_Lean_Widget_widgetInfosAt_x3f(v_text_3732_, v_val_3733_, v_line_3747_);
v___x_3749_ = lean_array_mk(v___x_3748_);
v_sz_3750_ = lean_array_size(v___x_3749_);
v___x_3751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v_text_3732_, v_env_3740_, v_sz_3750_, v___x_3744_, v___x_3749_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3760_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3756_ = l_Array_append___redArg(v_a_3746_, v_a_3752_);
lean_dec(v_a_3752_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3756_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3746_);
v_a_3761_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3751_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3751_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v_env_3740_);
lean_dec_ref(v_val_3733_);
lean_dec_ref(v_text_3732_);
lean_dec_ref(v_pos_3731_);
v_a_3769_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3745_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3745_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_env_3740_);
lean_dec_ref(v_val_3733_);
lean_dec_ref(v_text_3732_);
lean_dec_ref(v_pos_3731_);
v_a_3777_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3741_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3741_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object* v_pos_3785_, lean_object* v_text_3786_, lean_object* v_val_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3785_, v_text_3786_, v_val_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object* v_pos_3798_, lean_object* v_text_3799_, lean_object* v_x_3800_, lean_object* v___y_3801_){
_start:
{
if (lean_obj_tag(v_x_3800_) == 1)
{
lean_object* v_val_3806_; 
v_val_3806_ = lean_ctor_get(v_x_3800_, 0);
lean_inc(v_val_3806_);
lean_dec_ref_known(v_x_3800_, 1);
if (lean_obj_tag(v_val_3806_) == 0)
{
lean_object* v_i_3807_; 
v_i_3807_ = lean_ctor_get(v_val_3806_, 0);
if (lean_obj_tag(v_i_3807_) == 0)
{
lean_object* v_info_3808_; lean_object* v___f_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_info_3808_ = lean_ctor_get(v_i_3807_, 0);
lean_inc_ref(v_info_3808_);
v___f_3809_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3809_, 0, v_pos_3798_);
lean_closure_set(v___f_3809_, 1, v_text_3799_);
lean_closure_set(v___f_3809_, 2, v_val_3806_);
v___x_3810_ = lean_box(0);
v___x_3811_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__1));
v___x_3812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3812_, 0, v_info_3808_);
lean_ctor_set(v___x_3812_, 1, v___x_3810_);
lean_ctor_set(v___x_3812_, 2, v___x_3811_);
v___x_3813_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_3814_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_3812_, v___x_3813_, v___f_3809_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3831_; 
v_a_3823_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3825_ = v___x_3814_;
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3814_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = l_Lean_Server_RequestError_ofIoError(v_a_3823_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_dec_ref_known(v_val_3806_, 2);
lean_dec_ref(v_text_3799_);
lean_dec_ref(v_pos_3798_);
goto v___jp_3803_;
}
}
else
{
lean_dec(v_val_3806_);
lean_dec_ref(v_text_3799_);
lean_dec_ref(v_pos_3798_);
goto v___jp_3803_;
}
}
else
{
lean_dec(v_x_3800_);
lean_dec_ref(v_text_3799_);
lean_dec_ref(v_pos_3798_);
goto v___jp_3803_;
}
v___jp_3803_:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__0));
v___x_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
return v___x_3805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object* v_pos_3832_, lean_object* v_text_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3832_, v_text_3833_, v_x_3834_, v___y_3835_);
lean_dec_ref(v___y_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets(lean_object* v_pos_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v_a_3842_; lean_object* v_toEditableDocumentCore_3843_; lean_object* v_meta_3844_; lean_object* v_initSnap_3845_; lean_object* v_text_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3841_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_3839_);
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref(v___x_3841_);
v_toEditableDocumentCore_3843_ = lean_ctor_get(v_a_3842_, 0);
lean_inc_ref(v_toEditableDocumentCore_3843_);
lean_dec(v_a_3842_);
v_meta_3844_ = lean_ctor_get(v_toEditableDocumentCore_3843_, 0);
lean_inc_ref(v_meta_3844_);
v_initSnap_3845_ = lean_ctor_get(v_toEditableDocumentCore_3843_, 1);
lean_inc_ref(v_initSnap_3845_);
lean_dec_ref(v_toEditableDocumentCore_3843_);
v_text_3846_ = lean_ctor_get(v_meta_3844_, 3);
lean_inc_ref_n(v_text_3846_, 2);
lean_dec_ref(v_meta_3844_);
lean_inc_ref(v_pos_3838_);
v___f_3847_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3847_, 0, v_pos_3838_);
lean_closure_set(v___f_3847_, 1, v_text_3846_);
v___x_3848_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3846_, v_pos_3838_);
v___x_3849_ = 1;
v___x_3850_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_3845_, v_text_3846_, v___x_3848_, v___x_3849_);
v___x_3851_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3850_, v___f_3847_, v_a_3839_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object* v_pos_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_Widget_getWidgets(v_pos_3852_, v_a_3853_);
lean_dec_ref(v_a_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object* v_00_u03b1_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3864_, lean_object* v_x_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(v_00_u03b1_3864_, v_x_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object* v_val_3872_, lean_object* v___f_3873_, lean_object* v_x_3874_, lean_object* v___y_3875_){
_start:
{
if (lean_obj_tag(v_x_3874_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___f_3873_);
v_a_3877_ = lean_ctor_get(v_x_3874_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_x_3874_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v_x_3874_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v_x_3874_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set_tag(v___x_3879_, 1);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3901_; 
v_a_3885_ = lean_ctor_get(v_x_3874_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_x_3874_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3887_ = v_x_3874_;
v_isShared_3888_ = v_isSharedCheck_3901_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v_x_3874_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3901_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v_objects_3890_; lean_object* v_expireTime_3891_; lean_object* v___f_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v_fst_3895_; lean_object* v_snd_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
v___x_3889_ = lean_st_ref_take(v_val_3872_);
v_objects_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc_ref(v_objects_3890_);
v_expireTime_3891_ = lean_ctor_get(v___x_3889_, 1);
lean_inc(v_expireTime_3891_);
lean_dec(v___x_3889_);
v___f_3892_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_3892_, 0, v_expireTime_3891_);
v___x_3893_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_a_3885_, v_objects_3890_);
v___x_3894_ = l_Prod_map___redArg(v___f_3873_, v___f_3892_, v___x_3893_);
v_fst_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_fst_3895_);
v_snd_3896_ = lean_ctor_get(v___x_3894_, 1);
lean_inc(v_snd_3896_);
lean_dec_ref(v___x_3894_);
v___x_3897_ = lean_st_ref_put(v_val_3872_, v_snd_3896_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set_tag(v___x_3887_, 0);
lean_ctor_set(v___x_3887_, 0, v_fst_3895_);
v___x_3899_ = v___x_3887_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_fst_3895_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object* v_val_3902_, lean_object* v___f_3903_, lean_object* v_x_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_3902_, v___f_3903_, v_x_3904_, v___y_3905_);
lean_dec_ref(v___y_3905_);
lean_dec(v_val_3902_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object* v___f_3908_, lean_object* v_method_3909_, lean_object* v_handler_3910_, uint64_t v_seshId_3911_, lean_object* v_j_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_rpcSessions_3915_; lean_object* v___x_3916_; 
v_rpcSessions_3915_ = lean_ctor_get(v___y_3913_, 0);
v___x_3916_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_3915_, v_seshId_3911_);
if (lean_obj_tag(v___x_3916_) == 1)
{
lean_object* v_val_3917_; lean_object* v___f_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_val_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc_n(v_val_3917_, 2);
lean_dec_ref_known(v___x_3916_, 1);
v___f_3918_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3918_, 0, v_val_3917_);
lean_closure_set(v___f_3918_, 1, v___f_3908_);
v___x_3919_ = lean_st_ref_get(v_val_3917_);
lean_dec(v_val_3917_);
lean_dec(v___x_3919_);
lean_inc(v_j_3912_);
v___x_3920_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v_j_3912_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v___f_3918_);
lean_dec_ref(v_handler_3910_);
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3941_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3941_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
uint8_t v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3925_ = 3;
v___x_3926_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_3927_ = 1;
v___x_3928_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_3909_, v___x_3927_);
v___x_3929_ = lean_string_append(v___x_3926_, v___x_3928_);
lean_dec_ref(v___x_3928_);
v___x_3930_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_3931_ = lean_string_append(v___x_3929_, v___x_3930_);
v___x_3932_ = l_Lean_Json_compress(v_j_3912_);
v___x_3933_ = lean_string_append(v___x_3931_, v___x_3932_);
lean_dec_ref(v___x_3932_);
v___x_3934_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_3935_ = lean_string_append(v___x_3933_, v___x_3934_);
v___x_3936_ = lean_string_append(v___x_3935_, v_a_3921_);
lean_dec(v_a_3921_);
v___x_3937_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set_uint8(v___x_3937_, sizeof(void*)*1, v___x_3925_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set_tag(v___x_3923_, 1);
lean_ctor_set(v___x_3923_, 0, v___x_3937_);
v___x_3939_ = v___x_3923_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3943_; 
lean_dec(v_j_3912_);
lean_dec(v_method_3909_);
v_a_3942_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3920_, 1);
lean_inc_ref(v___y_3913_);
v___x_3943_ = lean_apply_3(v_handler_3910_, v_a_3942_, v___y_3913_, lean_box(0));
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_3944_, v___f_3918_, v___y_3913_);
return v___x_3945_;
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v___f_3918_);
v_a_3946_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3943_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3943_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec(v___x_3916_);
lean_dec(v_j_3912_);
lean_dec_ref(v_handler_3910_);
lean_dec(v_method_3909_);
lean_dec_ref(v___f_3908_);
v___x_3954_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v___f_3956_, lean_object* v_method_3957_, lean_object* v_handler_3958_, lean_object* v_seshId_3959_, lean_object* v_j_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint64_t v_seshId_boxed_3963_; lean_object* v_res_3964_; 
v_seshId_boxed_3963_ = lean_unbox_uint64(v_seshId_3959_);
lean_dec_ref(v_seshId_3959_);
v_res_3964_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v___f_3956_, v_method_3957_, v_handler_3958_, v_seshId_boxed_3963_, v_j_3960_, v___y_3961_);
lean_dec_ref(v___y_3961_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_3965_, lean_object* v_handler_3966_){
_start:
{
lean_object* v___f_3967_; lean_object* v___f_3968_; 
v___f_3967_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 7, 3);
lean_closure_set(v___f_3968_, 0, v___f_3967_);
lean_closure_set(v___f_3968_, 1, v_method_3965_);
lean_closure_set(v___f_3968_, 2, v_handler_3966_);
return v___f_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object* v_method_3969_, lean_object* v_handler_3970_){
_start:
{
lean_object* v___x_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v_errMsg_3977_; uint8_t v___x_3978_; 
v___x_3972_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_3973_ = 1;
lean_inc(v_method_3969_);
v___x_3974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_3969_, v___x_3973_);
v___x_3975_ = lean_string_append(v___x_3972_, v___x_3974_);
lean_dec_ref(v___x_3974_);
v___x_3976_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
v___x_3978_ = l_Lean_initializing();
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec_ref(v_handler_3970_);
lean_dec(v_method_3969_);
v___x_3979_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_3980_ = lean_string_append(v_errMsg_3977_, v___x_3979_);
v___x_3981_ = lean_mk_io_user_error(v___x_3980_);
v___x_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
return v___x_3982_;
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3983_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_3984_ = lean_st_ref_get(v___x_3983_);
v___x_3985_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_3984_, v_method_3969_);
lean_dec(v___x_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_dec_ref(v_errMsg_3977_);
lean_inc(v_method_3969_);
v___x_3986_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(v_method_3969_, v_handler_3970_);
v___x_3987_ = lean_st_ref_take(v___x_3983_);
v___x_3988_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_3987_, v_method_3969_, v___x_3986_);
v___x_3989_ = lean_st_ref_put(v___x_3983_, v___x_3988_);
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
else
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_handler_3970_);
lean_dec(v_method_3969_);
v___x_3991_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_3992_ = lean_string_append(v_errMsg_3977_, v___x_3991_);
v___x_3993_ = lean_mk_io_user_error(v___x_3992_);
v___x_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_3995_, lean_object* v_handler_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_3995_, v_handler_3996_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4007_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4008_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v___x_4006_, v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
return v_res_4010_;
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
