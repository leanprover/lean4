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
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_8_ = stack[0].m_obj;
lean_object* v_a_9_ = stack[1].m_obj;
lean_object* v_a_10_ = stack[2].m_obj;
lean_object* v_a_11_ = stack[3].m_obj;
lean_object* v_a_12_ = stack[4].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___boxed(lean_object* v_e_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_e_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_25_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(lean_object* v_e_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; uint8_t v___x_38_; uint8_t v___x_39_; lean_object* v___x_40_; 
v___x_37_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___closed__1));
v___x_38_ = 1;
v___x_39_ = 1;
v___x_40_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_37_, v_e_31_, v___x_38_, v___x_39_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
return v___x_40_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v_a_32_ = stack[1].m_obj;
lean_object* v_a_33_ = stack[2].m_obj;
lean_object* v_a_34_ = stack[3].m_obj;
lean_object* v_a_35_ = stack[4].m_obj;
lean_object* v_res_41_;
v_res_41_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_e_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe___boxed(lean_object* v_e_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_e_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_48_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(1);
v___x_53_ = lean_st_mk_ref(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_55_;
v_res_55_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_();
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2____boxed(lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2402277489____hygCtx___hyg_2_();
return v_res_57_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(uint64_t v_k_58_, lean_object* v_v_59_, lean_object* v_t_60_){
_start:
{
if (lean_obj_tag(v_t_60_) == 0)
{
lean_object* v_size_61_; lean_object* v_k_62_; lean_object* v_v_63_; lean_object* v_l_64_; lean_object* v_r_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_349_; 
v_size_61_ = lean_ctor_get(v_t_60_, 0);
v_k_62_ = lean_ctor_get(v_t_60_, 1);
v_v_63_ = lean_ctor_get(v_t_60_, 2);
v_l_64_ = lean_ctor_get(v_t_60_, 3);
v_r_65_ = lean_ctor_get(v_t_60_, 4);
v_isSharedCheck_349_ = !lean_is_exclusive(v_t_60_);
if (v_isSharedCheck_349_ == 0)
{
v___x_67_ = v_t_60_;
v_isShared_68_ = v_isSharedCheck_349_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_r_65_);
lean_inc(v_l_64_);
lean_inc(v_v_63_);
lean_inc(v_k_62_);
lean_inc(v_size_61_);
lean_dec(v_t_60_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_349_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint64_t v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_unbox_uint64(v_k_62_);
v___x_70_ = lean_uint64_dec_lt(v_k_58_, v___x_69_);
if (v___x_70_ == 0)
{
uint64_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_unbox_uint64(v_k_62_);
v___x_72_ = lean_uint64_dec_eq(v_k_58_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v_impl_73_; lean_object* v___x_74_; 
lean_dec(v_size_61_);
v_impl_73_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_58_, v_v_59_, v_r_65_);
v___x_74_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_64_) == 0)
{
lean_object* v_size_75_; lean_object* v_size_76_; lean_object* v_k_77_; lean_object* v_v_78_; lean_object* v_l_79_; lean_object* v_r_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_size_75_ = lean_ctor_get(v_l_64_, 0);
v_size_76_ = lean_ctor_get(v_impl_73_, 0);
v_k_77_ = lean_ctor_get(v_impl_73_, 1);
v_v_78_ = lean_ctor_get(v_impl_73_, 2);
v_l_79_ = lean_ctor_get(v_impl_73_, 3);
lean_inc(v_l_79_);
v_r_80_ = lean_ctor_get(v_impl_73_, 4);
v___x_81_ = lean_unsigned_to_nat(3u);
v___x_82_ = lean_nat_mul(v___x_81_, v_size_75_);
v___x_83_ = lean_nat_dec_lt(v___x_82_, v_size_76_);
lean_dec(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
lean_dec(v_l_79_);
v___x_84_ = lean_nat_add(v___x_74_, v_size_75_);
v___x_85_ = lean_nat_add(v___x_84_, v_size_76_);
lean_dec(v___x_84_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_impl_73_);
lean_ctor_set(v___x_67_, 0, v___x_85_);
v___x_87_ = v___x_67_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v_l_64_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v_impl_73_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
else
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_152_; 
lean_inc(v_r_80_);
lean_inc(v_v_78_);
lean_inc(v_k_77_);
lean_inc(v_size_76_);
v_isSharedCheck_152_ = !lean_is_exclusive(v_impl_73_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; lean_object* v_unused_156_; lean_object* v_unused_157_; 
v_unused_153_ = lean_ctor_get(v_impl_73_, 4);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_impl_73_, 3);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_impl_73_, 2);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_impl_73_, 1);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_impl_73_, 0);
lean_dec(v_unused_157_);
v___x_90_ = v_impl_73_;
v_isShared_91_ = v_isSharedCheck_152_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_impl_73_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_152_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_size_92_; lean_object* v_k_93_; lean_object* v_v_94_; lean_object* v_l_95_; lean_object* v_r_96_; lean_object* v_size_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_size_92_ = lean_ctor_get(v_l_79_, 0);
v_k_93_ = lean_ctor_get(v_l_79_, 1);
v_v_94_ = lean_ctor_get(v_l_79_, 2);
v_l_95_ = lean_ctor_get(v_l_79_, 3);
v_r_96_ = lean_ctor_get(v_l_79_, 4);
v_size_97_ = lean_ctor_get(v_r_80_, 0);
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_nat_mul(v___x_98_, v_size_97_);
v___x_100_ = lean_nat_dec_lt(v_size_92_, v___x_99_);
lean_dec(v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_128_; 
lean_inc(v_r_96_);
lean_inc(v_l_95_);
lean_inc(v_v_94_);
lean_inc(v_k_93_);
v_isSharedCheck_128_ = !lean_is_exclusive(v_l_79_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; lean_object* v_unused_130_; lean_object* v_unused_131_; lean_object* v_unused_132_; lean_object* v_unused_133_; 
v_unused_129_ = lean_ctor_get(v_l_79_, 4);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_l_79_, 3);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_l_79_, 2);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v_l_79_, 1);
lean_dec(v_unused_132_);
v_unused_133_ = lean_ctor_get(v_l_79_, 0);
lean_dec(v_unused_133_);
v___x_102_ = v_l_79_;
v_isShared_103_ = v_isSharedCheck_128_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_l_79_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_128_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_118_; 
v___x_104_ = lean_nat_add(v___x_74_, v_size_75_);
v___x_105_ = lean_nat_add(v___x_104_, v_size_76_);
lean_dec(v_size_76_);
if (lean_obj_tag(v_l_95_) == 0)
{
lean_object* v_size_126_; 
v_size_126_ = lean_ctor_get(v_l_95_, 0);
lean_inc(v_size_126_);
v___y_118_ = v_size_126_;
goto v___jp_117_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___y_118_ = v___x_127_;
goto v___jp_117_;
}
v___jp_106_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_nat_add(v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 4, v_r_80_);
lean_ctor_set(v___x_102_, 3, v_r_96_);
lean_ctor_set(v___x_102_, 2, v_v_78_);
lean_ctor_set(v___x_102_, 1, v_k_77_);
lean_ctor_set(v___x_102_, 0, v___x_110_);
v___x_112_ = v___x_102_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_77_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_78_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_r_96_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_r_80_);
v___x_112_ = v_reuseFailAlloc_116_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_114_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 4, v___x_112_);
lean_ctor_set(v___x_90_, 3, v___y_107_);
lean_ctor_set(v___x_90_, 2, v_v_94_);
lean_ctor_set(v___x_90_, 1, v_k_93_);
lean_ctor_set(v___x_90_, 0, v___x_105_);
v___x_114_ = v___x_90_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v___y_107_);
lean_ctor_set(v_reuseFailAlloc_115_, 4, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_119_ = lean_nat_add(v___x_104_, v___y_118_);
lean_dec(v___y_118_);
lean_dec(v___x_104_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_l_95_);
lean_ctor_set(v___x_67_, 0, v___x_119_);
v___x_121_ = v___x_67_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_l_64_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v_l_95_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; 
v___x_122_ = lean_nat_add(v___x_74_, v_size_97_);
if (lean_obj_tag(v_r_96_) == 0)
{
lean_object* v_size_123_; 
v_size_123_ = lean_ctor_get(v_r_96_, 0);
lean_inc(v_size_123_);
v___y_107_ = v___x_121_;
v___y_108_ = v___x_122_;
v___y_109_ = v_size_123_;
goto v___jp_106_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___y_107_ = v___x_121_;
v___y_108_ = v___x_122_;
v___y_109_ = v___x_124_;
goto v___jp_106_;
}
}
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
lean_del_object(v___x_67_);
v___x_134_ = lean_nat_add(v___x_74_, v_size_75_);
v___x_135_ = lean_nat_add(v___x_134_, v_size_76_);
lean_dec(v_size_76_);
v___x_136_ = lean_nat_add(v___x_134_, v_size_92_);
lean_dec(v___x_134_);
lean_inc_ref(v_l_64_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 4, v_l_79_);
lean_ctor_set(v___x_90_, 3, v_l_64_);
lean_ctor_set(v___x_90_, 2, v_v_63_);
lean_ctor_set(v___x_90_, 1, v_k_62_);
lean_ctor_set(v___x_90_, 0, v___x_136_);
v___x_138_ = v___x_90_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_151_, 3, v_l_64_);
lean_ctor_set(v_reuseFailAlloc_151_, 4, v_l_79_);
v___x_138_ = v_reuseFailAlloc_151_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_isSharedCheck_145_ = !lean_is_exclusive(v_l_64_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; lean_object* v_unused_147_; lean_object* v_unused_148_; lean_object* v_unused_149_; lean_object* v_unused_150_; 
v_unused_146_ = lean_ctor_get(v_l_64_, 4);
lean_dec(v_unused_146_);
v_unused_147_ = lean_ctor_get(v_l_64_, 3);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_l_64_, 2);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_l_64_, 1);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v_l_64_, 0);
lean_dec(v_unused_150_);
v___x_140_ = v_l_64_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_dec(v_l_64_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 4, v_r_80_);
lean_ctor_set(v___x_140_, 3, v___x_138_);
lean_ctor_set(v___x_140_, 2, v_v_78_);
lean_ctor_set(v___x_140_, 1, v_k_77_);
lean_ctor_set(v___x_140_, 0, v___x_135_);
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_77_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_78_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_r_80_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_158_; 
v_l_158_ = lean_ctor_get(v_impl_73_, 3);
lean_inc(v_l_158_);
if (lean_obj_tag(v_l_158_) == 0)
{
lean_object* v_r_159_; lean_object* v_k_160_; lean_object* v_v_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_184_; 
v_r_159_ = lean_ctor_get(v_impl_73_, 4);
v_k_160_ = lean_ctor_get(v_impl_73_, 1);
v_v_161_ = lean_ctor_get(v_impl_73_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v_impl_73_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_185_ = lean_ctor_get(v_impl_73_, 3);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_impl_73_, 0);
lean_dec(v_unused_186_);
v___x_163_ = v_impl_73_;
v_isShared_164_ = v_isSharedCheck_184_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_r_159_);
lean_inc(v_v_161_);
lean_inc(v_k_160_);
lean_dec(v_impl_73_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_184_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_180_; 
v_k_165_ = lean_ctor_get(v_l_158_, 1);
v_v_166_ = lean_ctor_get(v_l_158_, 2);
v_isSharedCheck_180_ = !lean_is_exclusive(v_l_158_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_181_ = lean_ctor_get(v_l_158_, 4);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_l_158_, 3);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_l_158_, 0);
lean_dec(v_unused_183_);
v___x_168_ = v_l_158_;
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_v_166_);
lean_inc(v_k_165_);
lean_dec(v_l_158_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_159_, 2);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 4, v_r_159_);
lean_ctor_set(v___x_168_, 3, v_r_159_);
lean_ctor_set(v___x_168_, 2, v_v_63_);
lean_ctor_set(v___x_168_, 1, v_k_62_);
lean_ctor_set(v___x_168_, 0, v___x_74_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_r_159_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_r_159_);
v___x_172_ = v_reuseFailAlloc_179_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
lean_inc(v_r_159_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 3, v_r_159_);
lean_ctor_set(v___x_163_, 0, v___x_74_);
v___x_174_ = v___x_163_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_k_160_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_v_161_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_r_159_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_r_159_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v___x_174_);
lean_ctor_set(v___x_67_, 3, v___x_172_);
lean_ctor_set(v___x_67_, 2, v_v_166_);
lean_ctor_set(v___x_67_, 1, v_k_165_);
lean_ctor_set(v___x_67_, 0, v___x_170_);
v___x_176_ = v___x_67_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
else
{
lean_object* v_r_187_; 
v_r_187_ = lean_ctor_get(v_impl_73_, 4);
lean_inc(v_r_187_);
if (lean_obj_tag(v_r_187_) == 0)
{
lean_object* v_k_188_; lean_object* v_v_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_200_; 
v_k_188_ = lean_ctor_get(v_impl_73_, 1);
v_v_189_ = lean_ctor_get(v_impl_73_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v_impl_73_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; lean_object* v_unused_203_; 
v_unused_201_ = lean_ctor_get(v_impl_73_, 4);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_impl_73_, 3);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_impl_73_, 0);
lean_dec(v_unused_203_);
v___x_191_ = v_impl_73_;
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_v_189_);
lean_inc(v_k_188_);
lean_dec(v_impl_73_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(3u);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v_l_158_);
lean_ctor_set(v___x_191_, 2, v_v_63_);
lean_ctor_set(v___x_191_, 1, v_k_62_);
lean_ctor_set(v___x_191_, 0, v___x_74_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_l_158_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_l_158_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_r_187_);
lean_ctor_set(v___x_67_, 3, v___x_195_);
lean_ctor_set(v___x_67_, 2, v_v_189_);
lean_ctor_set(v___x_67_, 1, v_k_188_);
lean_ctor_set(v___x_67_, 0, v___x_193_);
v___x_197_ = v___x_67_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v_r_187_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_unsigned_to_nat(2u);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_impl_73_);
lean_ctor_set(v___x_67_, 3, v_r_187_);
lean_ctor_set(v___x_67_, 0, v___x_204_);
v___x_206_ = v___x_67_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_r_187_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v_impl_73_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec(v_v_63_);
lean_dec(v_k_62_);
v___x_208_ = lean_box_uint64(v_k_58_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 2, v_v_59_);
lean_ctor_set(v___x_67_, 1, v___x_208_);
v___x_210_ = v___x_67_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_size_61_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_v_59_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_l_64_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_r_65_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_impl_212_; lean_object* v___x_213_; 
lean_dec(v_size_61_);
v_impl_212_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_58_, v_v_59_, v_l_64_);
v___x_213_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_65_) == 0)
{
lean_object* v_size_214_; lean_object* v_size_215_; lean_object* v_k_216_; lean_object* v_v_217_; lean_object* v_l_218_; lean_object* v_r_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_size_214_ = lean_ctor_get(v_r_65_, 0);
v_size_215_ = lean_ctor_get(v_impl_212_, 0);
v_k_216_ = lean_ctor_get(v_impl_212_, 1);
v_v_217_ = lean_ctor_get(v_impl_212_, 2);
v_l_218_ = lean_ctor_get(v_impl_212_, 3);
v_r_219_ = lean_ctor_get(v_impl_212_, 4);
lean_inc(v_r_219_);
v___x_220_ = lean_unsigned_to_nat(3u);
v___x_221_ = lean_nat_mul(v___x_220_, v_size_214_);
v___x_222_ = lean_nat_dec_lt(v___x_221_, v_size_215_);
lean_dec(v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
lean_dec(v_r_219_);
v___x_223_ = lean_nat_add(v___x_213_, v_size_215_);
v___x_224_ = lean_nat_add(v___x_223_, v_size_214_);
lean_dec(v___x_223_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 3, v_impl_212_);
lean_ctor_set(v___x_67_, 0, v___x_224_);
v___x_226_ = v___x_67_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_impl_212_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_r_65_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
else
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_293_; 
lean_inc(v_l_218_);
lean_inc(v_v_217_);
lean_inc(v_k_216_);
lean_inc(v_size_215_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_impl_212_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_294_ = lean_ctor_get(v_impl_212_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_impl_212_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_impl_212_, 2);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_impl_212_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_impl_212_, 0);
lean_dec(v_unused_298_);
v___x_229_ = v_impl_212_;
v_isShared_230_ = v_isSharedCheck_293_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_impl_212_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_293_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_size_231_; lean_object* v_size_232_; lean_object* v_k_233_; lean_object* v_v_234_; lean_object* v_l_235_; lean_object* v_r_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_size_231_ = lean_ctor_get(v_l_218_, 0);
v_size_232_ = lean_ctor_get(v_r_219_, 0);
v_k_233_ = lean_ctor_get(v_r_219_, 1);
v_v_234_ = lean_ctor_get(v_r_219_, 2);
v_l_235_ = lean_ctor_get(v_r_219_, 3);
v_r_236_ = lean_ctor_get(v_r_219_, 4);
v___x_237_ = lean_unsigned_to_nat(2u);
v___x_238_ = lean_nat_mul(v___x_237_, v_size_231_);
v___x_239_ = lean_nat_dec_lt(v_size_232_, v___x_238_);
lean_dec(v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_268_; 
lean_inc(v_r_236_);
lean_inc(v_l_235_);
lean_inc(v_v_234_);
lean_inc(v_k_233_);
v_isSharedCheck_268_ = !lean_is_exclusive(v_r_219_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; 
v_unused_269_ = lean_ctor_get(v_r_219_, 4);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_r_219_, 3);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_r_219_, 2);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_r_219_, 1);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_r_219_, 0);
lean_dec(v_unused_273_);
v___x_241_ = v_r_219_;
v_isShared_242_ = v_isSharedCheck_268_;
goto v_resetjp_240_;
}
else
{
lean_dec(v_r_219_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_268_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___x_256_; lean_object* v___y_258_; 
v___x_243_ = lean_nat_add(v___x_213_, v_size_215_);
lean_dec(v_size_215_);
v___x_244_ = lean_nat_add(v___x_243_, v_size_214_);
lean_dec(v___x_243_);
v___x_256_ = lean_nat_add(v___x_213_, v_size_231_);
if (lean_obj_tag(v_l_235_) == 0)
{
lean_object* v_size_266_; 
v_size_266_ = lean_ctor_get(v_l_235_, 0);
lean_inc(v_size_266_);
v___y_258_ = v_size_266_;
goto v___jp_257_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___y_258_ = v___x_267_;
goto v___jp_257_;
}
v___jp_245_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_nat_add(v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec(v___y_247_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 4, v_r_65_);
lean_ctor_set(v___x_241_, 3, v_r_236_);
lean_ctor_set(v___x_241_, 2, v_v_63_);
lean_ctor_set(v___x_241_, 1, v_k_62_);
lean_ctor_set(v___x_241_, 0, v___x_249_);
v___x_251_ = v___x_241_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_r_236_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_r_65_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v___x_251_);
lean_ctor_set(v___x_229_, 3, v___y_246_);
lean_ctor_set(v___x_229_, 2, v_v_234_);
lean_ctor_set(v___x_229_, 1, v_k_233_);
lean_ctor_set(v___x_229_, 0, v___x_244_);
v___x_253_ = v___x_229_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_233_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_234_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___y_246_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_nat_add(v___x_256_, v___y_258_);
lean_dec(v___y_258_);
lean_dec(v___x_256_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_l_235_);
lean_ctor_set(v___x_67_, 3, v_l_218_);
lean_ctor_set(v___x_67_, 2, v_v_217_);
lean_ctor_set(v___x_67_, 1, v_k_216_);
lean_ctor_set(v___x_67_, 0, v___x_259_);
v___x_261_ = v___x_67_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_k_216_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_v_217_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_l_218_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_l_235_);
v___x_261_ = v_reuseFailAlloc_265_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; 
v___x_262_ = lean_nat_add(v___x_213_, v_size_214_);
if (lean_obj_tag(v_r_236_) == 0)
{
lean_object* v_size_263_; 
v_size_263_ = lean_ctor_get(v_r_236_, 0);
lean_inc(v_size_263_);
v___y_246_ = v___x_261_;
v___y_247_ = v___x_262_;
v___y_248_ = v_size_263_;
goto v___jp_245_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___y_246_ = v___x_261_;
v___y_247_ = v___x_262_;
v___y_248_ = v___x_264_;
goto v___jp_245_;
}
}
}
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
lean_del_object(v___x_67_);
v___x_274_ = lean_nat_add(v___x_213_, v_size_215_);
lean_dec(v_size_215_);
v___x_275_ = lean_nat_add(v___x_274_, v_size_214_);
lean_dec(v___x_274_);
v___x_276_ = lean_nat_add(v___x_213_, v_size_214_);
v___x_277_ = lean_nat_add(v___x_276_, v_size_232_);
lean_dec(v___x_276_);
lean_inc_ref(v_r_65_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v_r_65_);
lean_ctor_set(v___x_229_, 3, v_r_219_);
lean_ctor_set(v___x_229_, 2, v_v_63_);
lean_ctor_set(v___x_229_, 1, v_k_62_);
lean_ctor_set(v___x_229_, 0, v___x_277_);
v___x_279_ = v___x_229_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_r_219_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_r_65_);
v___x_279_ = v_reuseFailAlloc_292_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_isSharedCheck_286_ = !lean_is_exclusive(v_r_65_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; 
v_unused_287_ = lean_ctor_get(v_r_65_, 4);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_r_65_, 3);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_r_65_, 2);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_r_65_, 1);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_r_65_, 0);
lean_dec(v_unused_291_);
v___x_281_ = v_r_65_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_r_65_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 4, v___x_279_);
lean_ctor_set(v___x_281_, 3, v_l_218_);
lean_ctor_set(v___x_281_, 2, v_v_217_);
lean_ctor_set(v___x_281_, 1, v_k_216_);
lean_ctor_set(v___x_281_, 0, v___x_275_);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_k_216_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_v_217_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_l_218_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v___x_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_299_; 
v_l_299_ = lean_ctor_get(v_impl_212_, 3);
if (lean_obj_tag(v_l_299_) == 0)
{
lean_object* v_r_300_; lean_object* v_k_301_; lean_object* v_v_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_313_; 
lean_inc_ref(v_l_299_);
v_r_300_ = lean_ctor_get(v_impl_212_, 4);
v_k_301_ = lean_ctor_get(v_impl_212_, 1);
v_v_302_ = lean_ctor_get(v_impl_212_, 2);
v_isSharedCheck_313_ = !lean_is_exclusive(v_impl_212_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_314_ = lean_ctor_get(v_impl_212_, 3);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_impl_212_, 0);
lean_dec(v_unused_315_);
v___x_304_ = v_impl_212_;
v_isShared_305_ = v_isSharedCheck_313_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_r_300_);
lean_inc(v_v_302_);
lean_inc(v_k_301_);
lean_dec(v_impl_212_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_313_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 3, v_r_300_);
lean_ctor_set(v___x_304_, 2, v_v_63_);
lean_ctor_set(v___x_304_, 1, v_k_62_);
lean_ctor_set(v___x_304_, 0, v___x_213_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_r_300_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_r_300_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v___x_308_);
lean_ctor_set(v___x_67_, 3, v_l_299_);
lean_ctor_set(v___x_67_, 2, v_v_302_);
lean_ctor_set(v___x_67_, 1, v_k_301_);
lean_ctor_set(v___x_67_, 0, v___x_306_);
v___x_310_ = v___x_67_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_k_301_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_v_302_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_r_316_; 
v_r_316_ = lean_ctor_get(v_impl_212_, 4);
lean_inc(v_r_316_);
if (lean_obj_tag(v_r_316_) == 0)
{
lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_341_; 
lean_inc(v_l_299_);
v_k_317_ = lean_ctor_get(v_impl_212_, 1);
v_v_318_ = lean_ctor_get(v_impl_212_, 2);
v_isSharedCheck_341_ = !lean_is_exclusive(v_impl_212_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_342_ = lean_ctor_get(v_impl_212_, 4);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_impl_212_, 3);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_impl_212_, 0);
lean_dec(v_unused_344_);
v___x_320_ = v_impl_212_;
v_isShared_321_ = v_isSharedCheck_341_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_v_318_);
lean_inc(v_k_317_);
lean_dec(v_impl_212_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_341_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_k_322_; lean_object* v_v_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_337_; 
v_k_322_ = lean_ctor_get(v_r_316_, 1);
v_v_323_ = lean_ctor_get(v_r_316_, 2);
v_isSharedCheck_337_ = !lean_is_exclusive(v_r_316_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_338_ = lean_ctor_get(v_r_316_, 4);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_r_316_, 3);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_r_316_, 0);
lean_dec(v_unused_340_);
v___x_325_ = v_r_316_;
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_v_323_);
lean_inc(v_k_322_);
lean_dec(v_r_316_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_unsigned_to_nat(3u);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_l_299_);
lean_ctor_set(v___x_325_, 3, v_l_299_);
lean_ctor_set(v___x_325_, 2, v_v_318_);
lean_ctor_set(v___x_325_, 1, v_k_317_);
lean_ctor_set(v___x_325_, 0, v___x_213_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_l_299_);
v___x_329_ = v_reuseFailAlloc_336_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_l_299_);
lean_ctor_set(v___x_320_, 2, v_v_63_);
lean_ctor_set(v___x_320_, 1, v_k_62_);
lean_ctor_set(v___x_320_, 0, v___x_213_);
v___x_331_ = v___x_320_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_l_299_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v___x_331_);
lean_ctor_set(v___x_67_, 3, v___x_329_);
lean_ctor_set(v___x_67_, 2, v_v_323_);
lean_ctor_set(v___x_67_, 1, v_k_322_);
lean_ctor_set(v___x_67_, 0, v___x_327_);
v___x_333_ = v___x_67_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_322_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_v_323_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_unsigned_to_nat(2u);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_r_316_);
lean_ctor_set(v___x_67_, 3, v_impl_212_);
lean_ctor_set(v___x_67_, 0, v___x_345_);
v___x_347_ = v___x_67_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_impl_212_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_r_316_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_box_uint64(v_k_58_);
v___x_352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_ctor_set(v___x_352_, 2, v_v_59_);
lean_ctor_set(v___x_352_, 3, v_t_60_);
lean_ctor_set(v___x_352_, 4, v_t_60_);
return v___x_352_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_58_ = stack[0].m_num;
lean_object* v_v_59_ = stack[1].m_obj;
lean_object* v_t_60_ = stack[2].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_58_, v_v_59_, v_t_60_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg___boxed(lean_object* v_k_354_, lean_object* v_v_355_, lean_object* v_t_356_){
_start:
{
uint64_t v_k_boxed_357_; lean_object* v_res_358_; 
v_k_boxed_357_ = lean_unbox_uint64(v_k_354_);
lean_dec_ref(v_k_354_);
v_res_358_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_boxed_357_, v_v_355_, v_t_356_);
return v_res_358_;
}
}
lean_object* l_Lean_Widget_addBuiltinModule(lean_object* v_id_359_, lean_object* v_m_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint64_t v_javascriptHash_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_362_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_363_ = lean_st_ref_take(v___x_362_);
v_javascriptHash_364_ = lean_ctor_get_uint64(v_m_360_, sizeof(void*)*1);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_id_359_);
lean_ctor_set(v___x_365_, 1, v_m_360_);
v___x_366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_javascriptHash_364_, v___x_365_, v___x_363_);
v___x_367_ = lean_st_ref_put(v___x_362_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Lean_Widget_addBuiltinModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_359_ = stack[0].m_obj;
lean_object* v_m_360_ = stack[1].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_Widget_addBuiltinModule(v_id_359_, v_m_360_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addBuiltinModule___boxed(lean_object* v_id_370_, lean_object* v_m_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Widget_addBuiltinModule(v_id_370_, v_m_371_);
return v_res_373_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0(lean_object* v_00_u03b2_374_, uint64_t v_k_375_, lean_object* v_v_376_, lean_object* v_t_377_, lean_object* v_hl_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v_k_375_, v_v_376_, v_t_377_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_375_ = stack[1].m_num;
lean_object* v_v_376_ = stack[2].m_obj;
lean_object* v_t_377_ = stack[3].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0(lean_box(0), v_k_375_, v_v_376_, v_t_377_, lean_box(0));
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___boxed(lean_object* v_00_u03b2_381_, lean_object* v_k_382_, lean_object* v_v_383_, lean_object* v_t_384_, lean_object* v_hl_385_){
_start:
{
uint64_t v_k_boxed_386_; lean_object* v_res_387_; 
v_k_boxed_386_ = lean_unbox_uint64(v_k_382_);
lean_dec_ref(v_k_382_);
v_res_387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0(v_00_u03b2_381_, v_k_boxed_386_, v_v_383_, v_t_384_, v_hl_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v_s_388_, lean_object* v_n_389_){
_start:
{
lean_object* v_fst_390_; lean_object* v_snd_391_; uint64_t v___x_392_; lean_object* v___x_393_; 
v_fst_390_ = lean_ctor_get(v_n_389_, 0);
lean_inc(v_fst_390_);
v_snd_391_ = lean_ctor_get(v_n_389_, 1);
lean_inc(v_snd_391_);
lean_dec_ref(v_n_389_);
v___x_392_ = lean_unbox_uint64(v_fst_390_);
lean_dec(v_fst_390_);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_392_, v_snd_391_, v_s_388_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v_es_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_array_mk(v_es_394_);
return v___x_395_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_396_, size_t v_i_397_, size_t v_stop_398_, lean_object* v_b_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_eq(v_i_397_, v_stop_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; uint64_t v___x_404_; lean_object* v___x_405_; size_t v___x_406_; size_t v___x_407_; 
v___x_401_ = lean_array_uget_borrowed(v_as_396_, v_i_397_);
v_fst_402_ = lean_ctor_get(v___x_401_, 0);
v_snd_403_ = lean_ctor_get(v___x_401_, 1);
v___x_404_ = lean_unbox_uint64(v_fst_402_);
lean_inc(v_snd_403_);
v___x_405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_404_, v_snd_403_, v_b_399_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_397_, v___x_406_);
v_i_397_ = v___x_407_;
v_b_399_ = v___x_405_;
goto _start;
}
else
{
return v_b_399_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_396_ = stack[0].m_obj;
size_t v_i_397_ = stack[1].m_num;
size_t v_stop_398_ = stack[2].m_num;
lean_object* v_b_399_ = stack[3].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(v_as_396_, v_i_397_, v_stop_398_, v_b_399_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_410_, lean_object* v_i_411_, lean_object* v_stop_412_, lean_object* v_b_413_){
_start:
{
size_t v_i_boxed_414_; size_t v_stop_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_stop_boxed_415_ = lean_unbox_usize(v_stop_412_);
lean_dec(v_stop_412_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(v_as_410_, v_i_boxed_414_, v_stop_boxed_415_, v_b_413_);
lean_dec_ref(v_as_410_);
return v_res_416_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(lean_object* v_as_417_, size_t v_i_418_, size_t v_stop_419_, lean_object* v_b_420_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_eq(v_i_418_, v_stop_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; uint64_t v___x_425_; lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_422_ = lean_array_uget_borrowed(v_as_417_, v_i_418_);
v_fst_423_ = lean_ctor_get(v___x_422_, 0);
v_snd_424_ = lean_ctor_get(v___x_422_, 1);
v___x_425_ = lean_unbox_uint64(v_fst_423_);
lean_inc(v_snd_424_);
v___x_426_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_425_, v_snd_424_, v_b_420_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_418_, v___x_427_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_spec__0(v_as_417_, v___x_428_, v_stop_419_, v___x_426_);
return v___x_429_;
}
else
{
return v_b_420_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_417_ = stack[0].m_obj;
size_t v_i_418_ = stack[1].m_num;
size_t v_stop_419_ = stack[2].m_num;
lean_object* v_b_420_ = stack[3].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v_as_417_, v_i_418_, v_stop_419_, v_b_420_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_stop_433_, lean_object* v_b_434_){
_start:
{
size_t v_i_boxed_435_; size_t v_stop_boxed_436_; lean_object* v_res_437_; 
v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_stop_boxed_436_ = lean_unbox_usize(v_stop_433_);
lean_dec(v_stop_433_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v_as_431_, v_i_boxed_435_, v_stop_boxed_436_, v_b_434_);
lean_dec_ref(v_as_431_);
return v_res_437_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(lean_object* v_as_438_, size_t v_i_439_, size_t v_stop_440_, lean_object* v_b_441_){
_start:
{
lean_object* v___y_443_; uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
v___x_450_ = lean_array_get_size(v___x_449_);
v___x_451_ = lean_nat_dec_lt(v___x_448_, v___x_450_);
if (v___x_451_ == 0)
{
v___y_443_ = v_b_441_;
goto v___jp_442_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = lean_nat_dec_le(v___x_450_, v___x_450_);
if (v___x_452_ == 0)
{
if (v___x_451_ == 0)
{
v___y_443_ = v_b_441_;
goto v___jp_442_;
}
else
{
size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((size_t)0ULL);
v___x_454_ = lean_usize_of_nat(v___x_450_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v___x_449_, v___x_453_, v___x_454_, v_b_441_);
v___y_443_ = v___x_455_;
goto v___jp_442_;
}
}
else
{
size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
v___x_456_ = ((size_t)0ULL);
v___x_457_ = lean_usize_of_nat(v___x_450_);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__0(v___x_449_, v___x_456_, v___x_457_, v_b_441_);
v___y_443_ = v___x_458_;
goto v___jp_442_;
}
}
}
else
{
return v_b_441_;
}
v___jp_442_:
{
size_t v___x_444_; size_t v___x_445_; 
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_439_, v___x_444_);
v_i_439_ = v___x_445_;
v_b_441_ = v___y_443_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_438_ = stack[0].m_obj;
size_t v_i_439_ = stack[1].m_num;
size_t v_stop_440_ = stack[2].m_num;
lean_object* v_b_441_ = stack[3].m_obj;
lean_object* v_res_459_;
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_as_438_, v_i_439_, v_stop_440_, v_b_441_);
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_460_, lean_object* v_i_461_, lean_object* v_stop_462_, lean_object* v_b_463_){
_start:
{
size_t v_i_boxed_464_; size_t v_stop_boxed_465_; lean_object* v_res_466_; 
v_i_boxed_464_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_stop_boxed_465_ = lean_unbox_usize(v_stop_462_);
lean_dec(v_stop_462_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_as_460_, v_i_boxed_464_, v_stop_boxed_465_, v_b_463_);
lean_dec_ref(v_as_460_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(lean_object* v___x_467_, lean_object* v_xss_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_box(1);
v___x_470_ = lean_array_get_size(v_xss_468_);
v___x_471_ = lean_nat_dec_lt(v___x_467_, v___x_470_);
if (v___x_471_ == 0)
{
return v___x_469_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = lean_nat_dec_le(v___x_470_, v___x_470_);
if (v___x_472_ == 0)
{
if (v___x_471_ == 0)
{
return v___x_469_;
}
else
{
size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((size_t)0ULL);
v___x_474_ = lean_usize_of_nat(v___x_470_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_xss_468_, v___x_473_, v___x_474_, v___x_469_);
return v___x_475_;
}
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((size_t)0ULL);
v___x_477_ = lean_usize_of_nat(v___x_470_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__spec__1(v_xss_468_, v___x_476_, v___x_477_, v___x_469_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v___x_479_, lean_object* v_xss_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(v___x_479_, v_xss_480_);
lean_dec_ref(v_xss_480_);
lean_dec(v___x_479_);
return v_res_481_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_));
v___x_523_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_524_;
v_res_524_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2____boxed(lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_925824488____hygCtx___hyg_2_();
return v_res_526_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_527_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_533_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
lean_ctor_set(v___x_533_, 3, v___x_532_);
lean_ctor_set(v___x_533_, 4, v___x_532_);
lean_ctor_set(v___x_533_, 5, v___x_532_);
return v___x_533_;
}
}
lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_nextMacroScope_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_traceState_542_; lean_object* v_recordedDeps_543_; lean_object* v_messages_544_; lean_object* v_infoState_545_; lean_object* v_snapshotTasks_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_572_; 
v___x_538_ = lean_st_ref_take(v___y_536_);
v_nextMacroScope_539_ = lean_ctor_get(v___x_538_, 1);
v_ngen_540_ = lean_ctor_get(v___x_538_, 2);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_538_, 3);
v_traceState_542_ = lean_ctor_get(v___x_538_, 4);
v_recordedDeps_543_ = lean_ctor_get(v___x_538_, 6);
v_messages_544_ = lean_ctor_get(v___x_538_, 7);
v_infoState_545_ = lean_ctor_get(v___x_538_, 8);
v_snapshotTasks_546_ = lean_ctor_get(v___x_538_, 9);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_573_ = lean_ctor_get(v___x_538_, 5);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v___x_538_, 0);
lean_dec(v_unused_574_);
v___x_548_ = v___x_538_;
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_snapshotTasks_546_);
lean_inc(v_infoState_545_);
lean_inc(v_messages_544_);
lean_inc(v_recordedDeps_543_);
lean_inc(v_traceState_542_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_nextMacroScope_539_);
lean_dec(v___x_538_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 5, v___x_550_);
lean_ctor_set(v___x_548_, 0, v_env_534_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_env_534_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_nextMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_traceState_542_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_571_, 6, v_recordedDeps_543_);
lean_ctor_set(v_reuseFailAlloc_571_, 7, v_messages_544_);
lean_ctor_set(v_reuseFailAlloc_571_, 8, v_infoState_545_);
lean_ctor_set(v_reuseFailAlloc_571_, 9, v_snapshotTasks_546_);
v___x_552_ = v_reuseFailAlloc_571_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_mctx_555_; lean_object* v_zetaDeltaFVarIds_556_; lean_object* v_postponed_557_; lean_object* v_diag_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_569_; 
v___x_553_ = lean_st_ref_put(v___y_536_, v___x_552_);
v___x_554_ = lean_st_ref_take(v___y_535_);
v_mctx_555_ = lean_ctor_get(v___x_554_, 0);
v_zetaDeltaFVarIds_556_ = lean_ctor_get(v___x_554_, 2);
v_postponed_557_ = lean_ctor_get(v___x_554_, 3);
v_diag_558_ = lean_ctor_get(v___x_554_, 4);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_554_, 1);
lean_dec(v_unused_570_);
v___x_560_ = v___x_554_;
v_isShared_561_ = v_isSharedCheck_569_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_diag_558_);
lean_inc(v_postponed_557_);
lean_inc(v_zetaDeltaFVarIds_556_);
lean_inc(v_mctx_555_);
lean_dec(v___x_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_569_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_563_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_mctx_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_zetaDeltaFVarIds_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_postponed_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_diag_558_);
v___x_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_st_ref_put(v___y_535_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_562_);
return v___x_567_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_534_ = stack[0].m_obj;
lean_object* v___y_535_ = stack[1].m_obj;
lean_object* v___y_536_ = stack[2].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_534_, v___y_535_, v___y_536_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
return v_res_580_;
}
}
lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(lean_object* v_env_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v_env_581_, v___y_583_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_581_ = stack[0].m_obj;
lean_object* v___y_582_ = stack[1].m_obj;
lean_object* v___y_583_ = stack[2].m_obj;
lean_object* v___y_584_ = stack[3].m_obj;
lean_object* v___y_585_ = stack[4].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(v_env_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1(v_env_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
lean_ctor_set(v___x_601_, 3, v___x_600_);
lean_ctor_set(v___x_601_, 4, v___x_599_);
lean_ctor_set(v___x_601_, 5, v___x_599_);
lean_ctor_set(v___x_601_, 6, v___x_599_);
lean_ctor_set(v___x_601_, 7, v___x_599_);
lean_ctor_set(v___x_601_, 8, v___x_599_);
lean_ctor_set(v___x_601_, 9, v___x_599_);
lean_ctor_set(v___x_601_, 10, v___x_599_);
lean_ctor_set(v___x_601_, 11, v___x_598_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(32u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_605_ = ((size_t)5ULL);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_unsigned_to_nat(32u);
v___x_608_ = lean_mk_empty_array_with_capacity(v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_610_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_606_);
lean_ctor_set(v___x_610_, 3, v___x_606_);
lean_ctor_set_usize(v___x_610_, 4, v___x_605_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_box(1);
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_611_);
return v___x_614_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; lean_object* v_toCold_620_; lean_object* v_env_621_; lean_object* v_options_622_; uint8_t v___x_623_; lean_object* v_env_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_619_ = lean_st_ref_get(v___y_617_);
v_toCold_620_ = lean_ctor_get(v___y_616_, 0);
v_env_621_ = lean_ctor_get(v___x_619_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_619_);
v_options_622_ = lean_ctor_get(v_toCold_620_, 2);
v___x_623_ = 0;
v_env_624_ = l_Lean_Environment_setRecordingDeps(v_env_621_, v___x_623_);
v___x_625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_622_);
v___x_627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_627_, 0, v_env_624_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
lean_ctor_set(v___x_627_, 3, v_options_622_);
v___x_628_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_msgData_615_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_615_ = stack[0].m_obj;
lean_object* v___y_616_ = stack[1].m_obj;
lean_object* v___y_617_ = stack[2].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msgData_615_, v___y_616_, v___y_617_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msgData_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_635_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_ref_640_; lean_object* v___x_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_ref_640_ = lean_ctor_get(v___y_637_, 2);
v___x_641_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0(v_msg_636_, v___y_637_, v___y_638_);
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_650_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
lean_inc(v_ref_640_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_ref_640_);
lean_ctor_set(v___x_646_, 1, v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
lean_ctor_set(v___x_644_, 0, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_636_ = stack[0].m_obj;
lean_object* v___y_637_ = stack[1].m_obj;
lean_object* v___y_638_ = stack[2].m_obj;
lean_object* v_res_651_;
v_res_651_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_636_, v___y_637_, v___y_638_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v_name_663_, lean_object* v_decl_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_668_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_669_ = l_Lean_MessageData_ofName(v_name_663_);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v___x_672_, v___y_665_, v___y_666_);
return v___x_673_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_name_663_ = stack[0].m_obj;
lean_object* v_decl_664_ = stack[1].m_obj;
lean_object* v___y_665_ = stack[2].m_obj;
lean_object* v___y_666_ = stack[3].m_obj;
lean_object* v_res_674_;
v_res_674_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_name_663_, v_decl_664_, v___y_665_, v___y_666_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_name_675_, lean_object* v_decl_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_name_675_, v_decl_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v_decl_676_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v_s_683_){
_start:
{
lean_object* v_addEntryFn_684_; lean_object* v_importedEntries_685_; lean_object* v_state_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_694_; 
v_addEntryFn_684_ = lean_ctor_get(v___x_681_, 3);
lean_inc(v_addEntryFn_684_);
lean_dec_ref(v___x_681_);
v_importedEntries_685_ = lean_ctor_get(v_s_683_, 0);
v_state_686_ = lean_ctor_get(v_s_683_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_s_683_);
if (v_isSharedCheck_694_ == 0)
{
v___x_688_ = v_s_683_;
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_state_686_);
lean_inc(v_importedEntries_685_);
lean_dec(v_s_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_state_690_; lean_object* v___x_692_; 
v_state_690_ = lean_apply_2(v_addEntryFn_684_, v_state_686_, v___x_682_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_state_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_importedEntries_685_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_state_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(lean_object* v_t_695_, uint64_t v_k_696_){
_start:
{
if (lean_obj_tag(v_t_695_) == 0)
{
lean_object* v_k_697_; lean_object* v_v_698_; lean_object* v_l_699_; lean_object* v_r_700_; uint64_t v___x_701_; uint8_t v___x_702_; 
v_k_697_ = lean_ctor_get(v_t_695_, 1);
v_v_698_ = lean_ctor_get(v_t_695_, 2);
v_l_699_ = lean_ctor_get(v_t_695_, 3);
v_r_700_ = lean_ctor_get(v_t_695_, 4);
v___x_701_ = lean_unbox_uint64(v_k_697_);
v___x_702_ = lean_uint64_dec_lt(v_k_696_, v___x_701_);
if (v___x_702_ == 0)
{
uint64_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_unbox_uint64(v_k_697_);
v___x_704_ = lean_uint64_dec_eq(v_k_696_, v___x_703_);
if (v___x_704_ == 0)
{
v_t_695_ = v_r_700_;
goto _start;
}
else
{
lean_object* v___x_706_; 
lean_inc(v_v_698_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_v_698_);
return v___x_706_;
}
}
else
{
v_t_695_ = v_l_699_;
goto _start;
}
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(0);
return v___x_708_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_695_ = stack[0].m_obj;
uint64_t v_k_696_ = stack[1].m_num;
lean_object* v_res_709_;
v_res_709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_695_, v_k_696_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_t_710_, lean_object* v_k_711_){
_start:
{
uint64_t v_k_boxed_712_; lean_object* v_res_713_; 
v_k_boxed_712_ = lean_unbox_uint64(v_k_711_);
lean_dec_ref(v_k_711_);
v_res_713_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_710_, v_k_boxed_712_);
lean_dec(v_t_710_);
return v_res_713_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_msgData_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v_env_721_; uint8_t v___x_722_; lean_object* v_env_723_; lean_object* v___x_724_; lean_object* v_toCold_725_; lean_object* v_mctx_726_; lean_object* v_lctx_727_; lean_object* v_options_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_720_ = lean_st_ref_get(v___y_718_);
v_env_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc_ref(v_env_721_);
lean_dec(v___x_720_);
v___x_722_ = 0;
v_env_723_ = l_Lean_Environment_setRecordingDeps(v_env_721_, v___x_722_);
v___x_724_ = lean_st_ref_get(v___y_716_);
v_toCold_725_ = lean_ctor_get(v___y_717_, 0);
v_mctx_726_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_mctx_726_);
lean_dec(v___x_724_);
v_lctx_727_ = lean_ctor_get(v___y_715_, 2);
v_options_728_ = lean_ctor_get(v_toCold_725_, 2);
lean_inc_ref(v_options_728_);
lean_inc_ref(v_lctx_727_);
v___x_729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_729_, 0, v_env_723_);
lean_ctor_set(v___x_729_, 1, v_mctx_726_);
lean_ctor_set(v___x_729_, 2, v_lctx_727_);
lean_ctor_set(v___x_729_, 3, v_options_728_);
v___x_730_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_msgData_714_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_714_ = stack[0].m_obj;
lean_object* v___y_715_ = stack[1].m_obj;
lean_object* v___y_716_ = stack[2].m_obj;
lean_object* v___y_717_ = stack[3].m_obj;
lean_object* v___y_718_ = stack[4].m_obj;
lean_object* v_res_732_;
v_res_732_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msgData_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_732_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msgData_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_ref_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_ref_746_ = lean_ctor_get(v___y_743_, 2);
v___x_747_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_inc(v_ref_746_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_ref_746_);
lean_ctor_set(v___x_752_, 1, v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_740_ = stack[0].m_obj;
lean_object* v___y_741_ = stack[1].m_obj;
lean_object* v___y_742_ = stack[2].m_obj;
lean_object* v___y_743_ = stack[3].m_obj;
lean_object* v___y_744_ = stack[4].m_obj;
lean_object* v_res_757_;
v_res_757_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_777_, uint8_t v_kind_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___y_790_; 
v___x_784_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_785_ = l_Lean_MessageData_ofName(v_name_777_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
switch(v_kind_778_)
{
case 0:
{
lean_object* v___x_797_; 
v___x_797_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_790_ = v___x_797_;
goto v___jp_789_;
}
case 1:
{
lean_object* v___x_798_; 
v___x_798_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__7));
v___y_790_ = v___x_798_;
goto v___jp_789_;
}
default: 
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__8));
v___y_790_ = v___x_799_;
goto v___jp_789_;
}
}
v___jp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_inc_ref(v___y_790_);
v___x_791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_791_, 0, v___y_790_);
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_788_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_795_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
return v___x_796_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_777_ = stack[0].m_obj;
uint8_t v_kind_778_ = stack[1].m_num;
lean_object* v___y_779_ = stack[2].m_obj;
lean_object* v___y_780_ = stack[3].m_obj;
lean_object* v___y_781_ = stack[4].m_obj;
lean_object* v___y_782_ = stack[5].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_777_, v_kind_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_801_, lean_object* v_kind_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v_kind_boxed_808_; lean_object* v_res_809_; 
v_kind_boxed_808_ = lean_unbox(v_kind_802_);
v_res_809_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_801_, v_kind_boxed_808_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_809_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(uint8_t v_suppressElabErrors_818_, uint8_t v___y_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 1)
{
lean_object* v_pre_821_; 
v_pre_821_ = lean_ctor_get(v_x_820_, 0);
switch(lean_obj_tag(v_pre_821_))
{
case 1:
{
lean_object* v_pre_822_; 
v_pre_822_ = lean_ctor_get(v_pre_821_, 0);
switch(lean_obj_tag(v_pre_822_))
{
case 0:
{
lean_object* v_str_823_; lean_object* v_str_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_str_823_ = lean_ctor_get(v_x_820_, 1);
v_str_824_ = lean_ctor_get(v_pre_821_, 1);
v___x_825_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_826_ = lean_string_dec_eq(v_str_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_828_ = lean_string_dec_eq(v_str_824_, v___x_827_);
if (v___x_828_ == 0)
{
return v___x_828_;
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_830_ = lean_string_dec_eq(v_str_823_, v___x_829_);
if (v___x_830_ == 0)
{
return v___x_830_;
}
else
{
return v_suppressElabErrors_818_;
}
}
}
else
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_832_ = lean_string_dec_eq(v_str_823_, v___x_831_);
if (v___x_832_ == 0)
{
return v___x_832_;
}
else
{
return v_suppressElabErrors_818_;
}
}
}
case 1:
{
lean_object* v_pre_833_; 
v_pre_833_ = lean_ctor_get(v_pre_822_, 0);
if (lean_obj_tag(v_pre_833_) == 0)
{
lean_object* v_str_834_; lean_object* v_str_835_; lean_object* v_str_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v_str_834_ = lean_ctor_get(v_x_820_, 1);
v_str_835_ = lean_ctor_get(v_pre_821_, 1);
v_str_836_ = lean_ctor_get(v_pre_822_, 1);
v___x_837_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_838_ = lean_string_dec_eq(v_str_836_, v___x_837_);
if (v___x_838_ == 0)
{
return v___x_838_;
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_840_ = lean_string_dec_eq(v_str_835_, v___x_839_);
if (v___x_840_ == 0)
{
return v___x_840_;
}
else
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__6));
v___x_842_ = lean_string_dec_eq(v_str_834_, v___x_841_);
if (v___x_842_ == 0)
{
return v___x_842_;
}
else
{
return v_suppressElabErrors_818_;
}
}
}
}
else
{
return v___y_819_;
}
}
default: 
{
return v___y_819_;
}
}
}
case 0:
{
lean_object* v_str_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_str_843_ = lean_ctor_get(v_x_820_, 1);
v___x_844_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___closed__7));
v___x_845_ = lean_string_dec_eq(v_str_843_, v___x_844_);
if (v___x_845_ == 0)
{
return v___x_845_;
}
else
{
return v_suppressElabErrors_818_;
}
}
default: 
{
return v___y_819_;
}
}
}
else
{
return v___y_819_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_818_ = stack[0].m_num;
uint8_t v___y_819_ = stack[1].m_num;
lean_object* v_x_820_ = stack[2].m_obj;
uint8_t v_res_846_;
v_res_846_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_818_, v___y_819_, v_x_820_);
stack->m_num = v_res_846_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_847_, lean_object* v___y_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_suppressElabErrors_boxed_850_; uint8_t v___y_11409__boxed_851_; uint8_t v_res_852_; lean_object* v_r_853_; 
v_suppressElabErrors_boxed_850_ = lean_unbox(v_suppressElabErrors_847_);
v___y_11409__boxed_851_ = lean_unbox(v___y_848_);
v_res_852_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_boxed_850_, v___y_11409__boxed_851_, v_x_849_);
lean_dec(v_x_849_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_opts_854_, lean_object* v_opt_855_){
_start:
{
lean_object* v_name_856_; lean_object* v_defValue_857_; lean_object* v_map_858_; lean_object* v___x_859_; 
v_name_856_ = lean_ctor_get(v_opt_855_, 0);
v_defValue_857_ = lean_ctor_get(v_opt_855_, 1);
v_map_858_ = lean_ctor_get(v_opts_854_, 0);
v___x_859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_858_, v_name_856_);
if (lean_obj_tag(v___x_859_) == 0)
{
uint8_t v___x_860_; 
v___x_860_ = lean_unbox(v_defValue_857_);
return v___x_860_;
}
else
{
lean_object* v_val_861_; 
v_val_861_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v___x_859_, 1);
if (lean_obj_tag(v_val_861_) == 1)
{
uint8_t v_v_862_; 
v_v_862_ = lean_ctor_get_uint8(v_val_861_, 0);
lean_dec_ref_known(v_val_861_, 0);
return v_v_862_;
}
else
{
uint8_t v___x_863_; 
lean_dec(v_val_861_);
v___x_863_ = lean_unbox(v_defValue_857_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_854_ = stack[0].m_obj;
lean_object* v_opt_855_ = stack[1].m_obj;
uint8_t v_res_864_;
v_res_864_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_opts_854_, v_opt_855_);
stack->m_num = v_res_864_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_opts_865_, lean_object* v_opt_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_opts_865_, v_opt_866_);
lean_dec_ref(v_opt_866_);
lean_dec_ref(v_opts_865_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_ref_870_, lean_object* v_msgData_871_, uint8_t v_severity_872_, uint8_t v_isSilent_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___y_883_; uint8_t v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v_toCold_887_; lean_object* v___y_888_; lean_object* v___y_917_; lean_object* v___y_918_; uint8_t v___y_919_; lean_object* v___y_920_; uint8_t v___y_921_; uint8_t v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; uint8_t v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; uint8_t v___y_947_; lean_object* v___y_948_; uint8_t v___y_949_; lean_object* v___y_950_; uint8_t v___y_954_; uint8_t v___y_955_; uint8_t v___y_956_; uint8_t v___x_967_; uint8_t v___y_969_; uint8_t v___y_970_; uint8_t v___y_971_; uint8_t v___y_973_; uint8_t v___x_981_; 
v___x_967_ = 2;
v___x_981_ = l_Lean_instBEqMessageSeverity_beq(v_severity_872_, v___x_967_);
if (v___x_981_ == 0)
{
v___y_973_ = v___x_981_;
goto v___jp_972_;
}
else
{
uint8_t v___x_982_; 
lean_inc_ref(v_msgData_871_);
v___x_982_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_871_);
v___y_973_ = v___x_982_;
goto v___jp_972_;
}
v___jp_879_:
{
lean_object* v_currNamespace_889_; lean_object* v_openDecls_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_env_895_; lean_object* v_nextMacroScope_896_; lean_object* v_ngen_897_; lean_object* v_auxDeclNGen_898_; lean_object* v_traceState_899_; lean_object* v_cache_900_; lean_object* v_recordedDeps_901_; lean_object* v_messages_902_; lean_object* v_infoState_903_; lean_object* v_snapshotTasks_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_915_; 
v_currNamespace_889_ = lean_ctor_get(v_toCold_887_, 4);
v_openDecls_890_ = lean_ctor_get(v_toCold_887_, 5);
lean_inc(v_openDecls_890_);
lean_inc(v_currNamespace_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_currNamespace_889_);
lean_ctor_set(v___x_891_, 1, v_openDecls_890_);
v___x_892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc_ref(v___y_886_);
v___x_893_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_893_, 0, v___y_886_);
lean_ctor_set(v___x_893_, 1, v___y_885_);
lean_ctor_set(v___x_893_, 2, v___y_882_);
lean_ctor_set(v___x_893_, 3, v___y_880_);
lean_ctor_set(v___x_893_, 4, v___x_892_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*5, v___y_883_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*5 + 1, v___y_884_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*5 + 2, v_isSilent_873_);
v___x_894_ = lean_st_ref_take(v___y_888_);
v_env_895_ = lean_ctor_get(v___x_894_, 0);
v_nextMacroScope_896_ = lean_ctor_get(v___x_894_, 1);
v_ngen_897_ = lean_ctor_get(v___x_894_, 2);
v_auxDeclNGen_898_ = lean_ctor_get(v___x_894_, 3);
v_traceState_899_ = lean_ctor_get(v___x_894_, 4);
v_cache_900_ = lean_ctor_get(v___x_894_, 5);
v_recordedDeps_901_ = lean_ctor_get(v___x_894_, 6);
v_messages_902_ = lean_ctor_get(v___x_894_, 7);
v_infoState_903_ = lean_ctor_get(v___x_894_, 8);
v_snapshotTasks_904_ = lean_ctor_get(v___x_894_, 9);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_915_ == 0)
{
v___x_906_ = v___x_894_;
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snapshotTasks_904_);
lean_inc(v_infoState_903_);
lean_inc(v_messages_902_);
lean_inc(v_recordedDeps_901_);
lean_inc(v_cache_900_);
lean_inc(v_traceState_899_);
lean_inc(v_auxDeclNGen_898_);
lean_inc(v_ngen_897_);
lean_inc(v_nextMacroScope_896_);
lean_inc(v_env_895_);
lean_dec(v___x_894_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_908_ = lean_box(0);
v___x_909_ = l_Lean_MessageLog_add(v___x_893_, v_messages_902_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 7, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_env_895_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_nextMacroScope_896_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_ngen_897_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_auxDeclNGen_898_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_traceState_899_);
lean_ctor_set(v_reuseFailAlloc_914_, 5, v_cache_900_);
lean_ctor_set(v_reuseFailAlloc_914_, 6, v_recordedDeps_901_);
lean_ctor_set(v_reuseFailAlloc_914_, 7, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_914_, 8, v_infoState_903_);
lean_ctor_set(v_reuseFailAlloc_914_, 9, v_snapshotTasks_904_);
v___x_911_ = v_reuseFailAlloc_914_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_st_ref_put(v___y_888_, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_908_);
return v___x_913_;
}
}
}
v___jp_916_:
{
lean_object* v_fileName_925_; lean_object* v_fileMap_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_942_; 
v_fileName_925_ = lean_ctor_get(v___y_923_, 0);
v_fileMap_926_ = lean_ctor_get(v___y_923_, 1);
v___x_927_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_871_);
v___x_928_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_spec__8(v___x_927_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_942_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_942_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_942_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc_ref_n(v_fileMap_926_, 2);
v___x_933_ = l_Lean_FileMap_toPosition(v_fileMap_926_, v___y_920_);
lean_dec(v___y_920_);
v___x_934_ = l_Lean_FileMap_toPosition(v_fileMap_926_, v___y_924_);
lean_dec(v___y_924_);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
if (v___y_919_ == 0)
{
lean_del_object(v___x_931_);
lean_dec_ref(v___y_917_);
v___y_880_ = v___x_936_;
v___y_881_ = v_a_929_;
v___y_882_ = v___x_935_;
v___y_883_ = v___y_921_;
v___y_884_ = v___y_922_;
v___y_885_ = v___x_933_;
v___y_886_ = v_fileName_925_;
v_toCold_887_ = v___y_918_;
v___y_888_ = v___y_877_;
goto v___jp_879_;
}
else
{
uint8_t v___x_937_; 
lean_inc(v_a_929_);
v___x_937_ = l_Lean_MessageData_hasTag(v___y_917_, v_a_929_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_940_; 
lean_dec_ref_known(v___x_935_, 1);
lean_dec_ref(v___x_933_);
lean_dec(v_a_929_);
v___x_938_ = lean_box(0);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_938_);
v___x_940_ = v___x_931_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_del_object(v___x_931_);
v___y_880_ = v___x_936_;
v___y_881_ = v_a_929_;
v___y_882_ = v___x_935_;
v___y_883_ = v___y_921_;
v___y_884_ = v___y_922_;
v___y_885_ = v___x_933_;
v___y_886_ = v_fileName_925_;
v_toCold_887_ = v___y_918_;
v___y_888_ = v___y_877_;
goto v___jp_879_;
}
}
}
}
v___jp_943_:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Syntax_getTailPos_x3f(v___y_948_, v___y_947_);
lean_dec(v___y_948_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_inc(v___y_950_);
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_950_;
v___y_921_ = v___y_947_;
v___y_922_ = v___y_949_;
v___y_923_ = v___y_946_;
v___y_924_ = v___y_950_;
goto v___jp_916_;
}
else
{
lean_object* v_val_952_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_951_, 1);
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_950_;
v___y_921_ = v___y_947_;
v___y_922_ = v___y_949_;
v___y_923_ = v___y_946_;
v___y_924_ = v_val_952_;
goto v___jp_916_;
}
}
v___jp_953_:
{
lean_object* v_toCold_957_; lean_object* v_ref_958_; uint8_t v_suppressElabErrors_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___f_962_; lean_object* v_ref_963_; lean_object* v___x_964_; 
v_toCold_957_ = lean_ctor_get(v___y_876_, 0);
v_ref_958_ = lean_ctor_get(v___y_876_, 2);
v_suppressElabErrors_959_ = lean_ctor_get_uint8(v___y_876_, sizeof(void*)*3 + 2);
v___x_960_ = lean_box(v_suppressElabErrors_959_);
v___x_961_ = lean_box(v___y_954_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_962_, 0, v___x_960_);
lean_closure_set(v___f_962_, 1, v___x_961_);
v_ref_963_ = l_Lean_replaceRef(v_ref_870_, v_ref_958_);
v___x_964_ = l_Lean_Syntax_getPos_x3f(v_ref_963_, v___y_955_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v___y_944_ = v_suppressElabErrors_959_;
v___y_945_ = v___f_962_;
v___y_946_ = v_toCold_957_;
v___y_947_ = v___y_955_;
v___y_948_ = v_ref_963_;
v___y_949_ = v___y_956_;
v___y_950_ = v___x_965_;
goto v___jp_943_;
}
else
{
lean_object* v_val_966_; 
v_val_966_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v___x_964_, 1);
v___y_944_ = v_suppressElabErrors_959_;
v___y_945_ = v___f_962_;
v___y_946_ = v_toCold_957_;
v___y_947_ = v___y_955_;
v___y_948_ = v_ref_963_;
v___y_949_ = v___y_956_;
v___y_950_ = v_val_966_;
goto v___jp_943_;
}
}
v___jp_968_:
{
if (v___y_971_ == 0)
{
v___y_954_ = v___y_969_;
v___y_955_ = v___y_970_;
v___y_956_ = v_severity_872_;
goto v___jp_953_;
}
else
{
v___y_954_ = v___y_969_;
v___y_955_ = v___y_970_;
v___y_956_ = v___x_967_;
goto v___jp_953_;
}
}
v___jp_972_:
{
if (v___y_973_ == 0)
{
uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_974_ = 1;
v___x_975_ = l_Lean_instBEqMessageSeverity_beq(v_severity_872_, v___x_974_);
if (v___x_975_ == 0)
{
v___y_969_ = v___y_973_;
v___y_970_ = v___y_973_;
v___y_971_ = v___x_975_;
goto v___jp_968_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_876_);
v___x_977_ = l_Lean_warningAsError;
v___x_978_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v___x_976_, v___x_977_);
lean_dec_ref(v___x_976_);
v___y_969_ = v___y_973_;
v___y_970_ = v___y_973_;
v___y_971_ = v___x_978_;
goto v___jp_968_;
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v_msgData_871_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_870_ = stack[0].m_obj;
lean_object* v_msgData_871_ = stack[1].m_obj;
uint8_t v_severity_872_ = stack[2].m_num;
uint8_t v_isSilent_873_ = stack[3].m_num;
lean_object* v___y_874_ = stack[4].m_obj;
lean_object* v___y_875_ = stack[5].m_obj;
lean_object* v___y_876_ = stack[6].m_obj;
lean_object* v___y_877_ = stack[7].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_870_, v_msgData_871_, v_severity_872_, v_isSilent_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_ref_984_, lean_object* v_msgData_985_, lean_object* v_severity_986_, lean_object* v_isSilent_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v_severity_boxed_993_; uint8_t v_isSilent_boxed_994_; lean_object* v_res_995_; 
v_severity_boxed_993_ = lean_unbox(v_severity_986_);
v_isSilent_boxed_994_ = lean_unbox(v_isSilent_987_);
v_res_995_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_984_, v_msgData_985_, v_severity_boxed_993_, v_isSilent_boxed_994_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_ref_984_);
return v_res_995_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_msgData_996_, uint8_t v_severity_997_, uint8_t v_isSilent_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_ref_1004_; lean_object* v___x_1005_; 
v_ref_1004_ = lean_ctor_get(v___y_1001_, 2);
v___x_1005_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_ref_1004_, v_msgData_996_, v_severity_997_, v_isSilent_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_996_ = stack[0].m_obj;
uint8_t v_severity_997_ = stack[1].m_num;
uint8_t v_isSilent_998_ = stack[2].m_num;
lean_object* v___y_999_ = stack[3].m_obj;
lean_object* v___y_1000_ = stack[4].m_obj;
lean_object* v___y_1001_ = stack[5].m_obj;
lean_object* v___y_1002_ = stack[6].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_996_, v_severity_997_, v_isSilent_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_msgData_1007_, lean_object* v_severity_1008_, lean_object* v_isSilent_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v_severity_boxed_1015_; uint8_t v_isSilent_boxed_1016_; lean_object* v_res_1017_; 
v_severity_boxed_1015_ = lean_unbox(v_severity_1008_);
v_isSilent_boxed_1016_ = lean_unbox(v_isSilent_1009_);
v_res_1017_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_1007_, v_severity_boxed_1015_, v_isSilent_boxed_1016_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1017_;
}
}
lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(lean_object* v_msgData_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = 1;
v___x_1025_ = 0;
v___x_1026_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4(v_msgData_1018_, v___x_1024_, v___x_1025_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1018_ = stack[0].m_obj;
lean_object* v___y_1019_ = stack[1].m_obj;
lean_object* v___y_1020_ = stack[2].m_obj;
lean_object* v___y_1021_ = stack[3].m_obj;
lean_object* v___y_1022_ = stack[4].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v_msgData_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3___boxed(lean_object* v_msgData_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v_msgData_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__7_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t v_builtin_1047_, lean_object* v_decl_1048_, uint8_t v___x_1049_, lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v_stx_1052_, uint8_t v_kind_1053_, lean_object* v_name_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1052_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1162_) == 0)
{
uint8_t v___x_1163_; uint8_t v___x_1164_; 
lean_dec_ref_known(v___x_1162_, 1);
v___x_1163_ = 0;
v___x_1164_ = l_Lean_instBEqAttributeKind_beq(v_kind_1053_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
lean_dec(v_decl_1048_);
v___x_1165_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_1054_, v_kind_1053_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1165_;
}
else
{
lean_dec(v_name_1054_);
goto v___jp_1124_;
}
}
else
{
lean_dec(v_name_1054_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
lean_dec(v_decl_1048_);
return v___x_1162_;
}
v___jp_1060_:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_st_ref_get(v___y_1067_);
if (v_builtin_1047_ == 0)
{
lean_object* v_env_1069_; uint64_t v_javascriptHash_1070_; lean_object* v___x_1071_; lean_object* v_toEnvExtension_1072_; lean_object* v_asyncMode_1073_; uint8_t v_logWrites_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; 
lean_dec(v___y_1061_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
v_env_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc_ref(v_env_1069_);
lean_dec(v___x_1068_);
v_javascriptHash_1070_ = lean_ctor_get_uint64(v___y_1062_, sizeof(void*)*1);
lean_dec_ref(v___y_1062_);
v___x_1071_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1072_ = lean_ctor_get(v___x_1071_, 0);
v_asyncMode_1073_ = lean_ctor_get(v_toEnvExtension_1072_, 2);
v_logWrites_1074_ = lean_ctor_get_uint8(v_toEnvExtension_1072_, sizeof(void*)*6);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_decl_1048_);
lean_ctor_set(v___x_1075_, 1, v___y_1063_);
v___x_1076_ = lean_box_uint64(v_javascriptHash_1070_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
v___f_1078_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1078_, 0, v___x_1071_);
lean_closure_set(v___f_1078_, 1, v___x_1077_);
v___x_1079_ = lean_box(0);
if (v_logWrites_1074_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_inc_ref(v_toEnvExtension_1072_);
v___x_1080_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1072_, v_env_1069_, v___f_1078_, v_asyncMode_1073_, v___x_1079_, v___x_1049_);
v___x_1081_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v___x_1080_, v___y_1065_, v___y_1067_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_inc_ref_n(v_toEnvExtension_1072_, 2);
v___x_1082_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1072_, v_env_1069_);
lean_dec_ref(v_env_1069_);
v___x_1083_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1072_, v___x_1082_, v___f_1078_, v_asyncMode_1073_, v___x_1079_, v___x_1049_);
v___x_1084_ = l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg(v___x_1083_, v___y_1065_, v___y_1067_);
return v___x_1084_;
}
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v___x_1068_);
lean_dec_ref(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_n(v_decl_1048_, 2);
v___x_1085_ = l_Lean_mkConst(v_decl_1048_, v___y_1061_);
v___x_1086_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1087_ = l_Lean_Name_mkStr3(v___x_1050_, v___x_1051_, v___x_1086_);
v___x_1088_ = l_Lean_mkConst(v___x_1087_, v___y_1061_);
v___x_1089_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_decl_1048_);
v___x_1090_ = l_Lean_mkAppB(v___x_1088_, v___x_1089_, v___x_1085_);
v___x_1091_ = l_Lean_declareBuiltin(v_decl_1048_, v___x_1090_, v___y_1066_, v___y_1067_);
return v___x_1091_;
}
}
v___jp_1092_:
{
lean_object* v___x_1101_; lean_object* v_toEnvExtension_1102_; lean_object* v_asyncMode_1103_; uint64_t v_javascriptHash_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1101_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1102_ = lean_ctor_get(v___x_1101_, 0);
v_asyncMode_1103_ = lean_ctor_get(v_toEnvExtension_1102_, 2);
v_javascriptHash_1104_ = lean_ctor_get_uint64(v___y_1095_, sizeof(void*)*1);
v___x_1105_ = lean_box(1);
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1105_, v___x_1101_, v___y_1093_, v_asyncMode_1103_, v___x_1106_);
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1107_, v_javascriptHash_1104_);
lean_dec(v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v_fst_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1122_; 
v_val_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v_fst_1110_ = lean_ctor_get(v_val_1109_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_val_1109_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_val_1109_, 1);
lean_dec(v_unused_1123_);
v___x_1112_ = v_val_1109_;
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_fst_1110_);
lean_dec(v_val_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1114_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1115_ = l_Lean_MessageData_ofConstName(v_fst_1110_, v___x_1049_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 7);
lean_ctor_set(v___x_1112_, 1, v___x_1115_);
lean_ctor_set(v___x_1112_, 0, v___x_1114_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v___x_1119_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_dec_ref_known(v___x_1120_, 1);
v___y_1061_ = v___y_1094_;
v___y_1062_ = v___y_1095_;
v___y_1063_ = v___y_1096_;
v___y_1064_ = v___y_1097_;
v___y_1065_ = v___y_1098_;
v___y_1066_ = v___y_1099_;
v___y_1067_ = v___y_1100_;
goto v___jp_1060_;
}
else
{
lean_dec_ref(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
lean_dec(v_decl_1048_);
return v___x_1120_;
}
}
}
}
else
{
lean_dec(v___x_1108_);
v___y_1061_ = v___y_1094_;
v___y_1062_ = v___y_1095_;
v___y_1063_ = v___y_1096_;
v___y_1064_ = v___y_1097_;
v___y_1065_ = v___y_1098_;
v___y_1066_ = v___y_1099_;
v___y_1067_ = v___y_1100_;
goto v___jp_1060_;
}
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1126_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__6_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
lean_inc_ref(v___x_1051_);
lean_inc_ref(v___x_1050_);
v___x_1127_ = l_Lean_Name_mkStr4(v___x_1050_, v___x_1051_, v___x_1125_, v___x_1126_);
v___x_1128_ = lean_box(0);
lean_inc(v_decl_1048_);
v___x_1129_ = l_Lean_Expr_const___override(v_decl_1048_, v___x_1128_);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_mk_empty_array_with_capacity(v___x_1130_);
v___x_1132_ = lean_array_push(v___x_1131_, v___x_1129_);
v___x_1133_ = l_Lean_Meta_mkAppM(v___x_1127_, v___x_1132_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_n(v_a_1134_, 2);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_1134_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = lean_st_ref_get(v___y_1058_);
if (v_builtin_1047_ == 0)
{
lean_object* v_env_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint64_t v_javascriptHash_1141_; lean_object* v___x_1142_; 
v_env_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_env_1138_);
lean_dec(v___x_1137_);
v___x_1139_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1140_ = lean_st_ref_get(v___x_1139_);
v_javascriptHash_1141_ = lean_ctor_get_uint64(v_a_1136_, sizeof(void*)*1);
v___x_1142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1140_, v_javascriptHash_1141_);
lean_dec(v___x_1140_);
if (lean_obj_tag(v___x_1142_) == 1)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref_known(v___x_1142_, 1);
v___x_1143_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__8_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1144_ = l_Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3(v___x_1143_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec_ref_known(v___x_1144_, 1);
v___y_1093_ = v_env_1138_;
v___y_1094_ = v___x_1128_;
v___y_1095_ = v_a_1136_;
v___y_1096_ = v_a_1134_;
v___y_1097_ = v___y_1055_;
v___y_1098_ = v___y_1056_;
v___y_1099_ = v___y_1057_;
v___y_1100_ = v___y_1058_;
goto v___jp_1092_;
}
else
{
lean_dec_ref(v_env_1138_);
lean_dec(v_a_1136_);
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
lean_dec(v_decl_1048_);
return v___x_1144_;
}
}
else
{
lean_dec(v___x_1142_);
v___y_1093_ = v_env_1138_;
v___y_1094_ = v___x_1128_;
v___y_1095_ = v_a_1136_;
v___y_1096_ = v_a_1134_;
v___y_1097_ = v___y_1055_;
v___y_1098_ = v___y_1056_;
v___y_1099_ = v___y_1057_;
v___y_1100_ = v___y_1058_;
goto v___jp_1092_;
}
}
else
{
lean_object* v_env_1145_; 
v_env_1145_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_env_1145_);
lean_dec(v___x_1137_);
v___y_1093_ = v_env_1145_;
v___y_1094_ = v___x_1128_;
v___y_1095_ = v_a_1136_;
v___y_1096_ = v_a_1134_;
v___y_1097_ = v___y_1055_;
v___y_1098_ = v___y_1056_;
v___y_1099_ = v___y_1057_;
v___y_1100_ = v___y_1058_;
goto v___jp_1092_;
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
lean_dec(v_decl_1048_);
v_a_1146_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1135_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1135_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1050_);
lean_dec(v_decl_1048_);
v_a_1154_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1133_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1133_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v_builtin_1047_ = stack[0].m_num;
lean_object* v_decl_1048_ = stack[1].m_obj;
uint8_t v___x_1049_ = stack[2].m_num;
lean_object* v___x_1050_ = stack[3].m_obj;
lean_object* v___x_1051_ = stack[4].m_obj;
lean_object* v_stx_1052_ = stack[5].m_obj;
uint8_t v_kind_1053_ = stack[6].m_num;
lean_object* v_name_1054_ = stack[7].m_obj;
lean_object* v___y_1055_ = stack[8].m_obj;
lean_object* v___y_1056_ = stack[9].m_obj;
lean_object* v___y_1057_ = stack[10].m_obj;
lean_object* v___y_1058_ = stack[11].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_1047_, v_decl_1048_, v___x_1049_, v___x_1050_, v___x_1051_, v_stx_1052_, v_kind_1053_, v_name_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_builtin_1167_, lean_object* v_decl_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v___x_1171_, lean_object* v_stx_1172_, lean_object* v_kind_1173_, lean_object* v_name_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v_builtin_boxed_1180_; uint8_t v___x_11903__boxed_1181_; uint8_t v_kind_boxed_1182_; lean_object* v_res_1183_; 
v_builtin_boxed_1180_ = lean_unbox(v_builtin_1167_);
v___x_11903__boxed_1181_ = lean_unbox(v___x_1169_);
v_kind_boxed_1182_ = lean_unbox(v_kind_1173_);
v_res_1183_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_boxed_1180_, v_decl_1168_, v___x_11903__boxed_1181_, v___x_1170_, v___x_1171_, v_stx_1172_, v_kind_boxed_1182_, v_name_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1183_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(lean_object* v___y_1184_, uint8_t v_isExporting_1185_, lean_object* v___x_1186_, lean_object* v___y_1187_, lean_object* v___x_1188_, lean_object* v_a_x3f_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v_nextMacroScope_1193_; lean_object* v_ngen_1194_; lean_object* v_auxDeclNGen_1195_; lean_object* v_traceState_1196_; lean_object* v_recordedDeps_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1225_; 
v___x_1191_ = lean_st_ref_take(v___y_1184_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1193_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1194_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1195_ = lean_ctor_get(v___x_1191_, 3);
v_traceState_1196_ = lean_ctor_get(v___x_1191_, 4);
v_recordedDeps_1197_ = lean_ctor_get(v___x_1191_, 6);
v_messages_1198_ = lean_ctor_get(v___x_1191_, 7);
v_infoState_1199_ = lean_ctor_get(v___x_1191_, 8);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1191_, 9);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1191_, 5);
lean_dec(v_unused_1226_);
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1225_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_recordedDeps_1197_);
lean_inc(v_traceState_1196_);
lean_inc(v_auxDeclNGen_1195_);
lean_inc(v_ngen_1194_);
lean_inc(v_nextMacroScope_1193_);
lean_inc(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1225_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = l_Lean_Environment_setExporting(v_env_1192_, v_isExporting_1185_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 5, v___x_1186_);
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_nextMacroScope_1193_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_ngen_1194_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_auxDeclNGen_1195_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_traceState_1196_);
lean_ctor_set(v_reuseFailAlloc_1224_, 5, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1224_, 6, v_recordedDeps_1197_);
lean_ctor_set(v_reuseFailAlloc_1224_, 7, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1224_, 8, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1224_, 9, v_snapshotTasks_1200_);
v___x_1206_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_mctx_1209_; lean_object* v_zetaDeltaFVarIds_1210_; lean_object* v_postponed_1211_; lean_object* v_diag_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v___x_1207_ = lean_st_ref_put(v___y_1184_, v___x_1206_);
v___x_1208_ = lean_st_ref_take(v___y_1187_);
v_mctx_1209_ = lean_ctor_get(v___x_1208_, 0);
v_zetaDeltaFVarIds_1210_ = lean_ctor_get(v___x_1208_, 2);
v_postponed_1211_ = lean_ctor_get(v___x_1208_, 3);
v_diag_1212_ = lean_ctor_get(v___x_1208_, 4);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1223_);
v___x_1214_ = v___x_1208_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_diag_1212_);
lean_inc(v_postponed_1211_);
lean_inc(v_zetaDeltaFVarIds_1210_);
lean_inc(v_mctx_1209_);
lean_dec(v___x_1208_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1188_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_mctx_1209_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_zetaDeltaFVarIds_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_postponed_1211_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_diag_1212_);
v___x_1218_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_st_ref_put(v___y_1187_, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1216_);
return v___x_1220_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1184_ = stack[0].m_obj;
uint8_t v_isExporting_1185_ = stack[1].m_num;
lean_object* v___x_1186_ = stack[2].m_obj;
lean_object* v___y_1187_ = stack[3].m_obj;
lean_object* v___x_1188_ = stack[4].m_obj;
lean_object* v_a_x3f_1189_ = stack[5].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1184_, v_isExporting_1185_, v___x_1186_, v___y_1187_, v___x_1188_, v_a_x3f_1189_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0___boxed(lean_object* v___y_1228_, lean_object* v_isExporting_1229_, lean_object* v___x_1230_, lean_object* v___y_1231_, lean_object* v___x_1232_, lean_object* v_a_x3f_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_isExporting_boxed_1235_; lean_object* v_res_1236_; 
v_isExporting_boxed_1235_ = lean_unbox(v_isExporting_1229_);
v_res_1236_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1228_, v_isExporting_boxed_1235_, v___x_1230_, v___y_1231_, v___x_1232_, v_a_x3f_1233_);
lean_dec(v_a_x3f_1233_);
lean_dec(v___y_1231_);
lean_dec(v___y_1228_);
return v_res_1236_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(lean_object* v_x_1237_, uint8_t v_isExporting_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v_env_1245_; lean_object* v___x_1246_; uint8_t v_isModule_1247_; 
v___x_1244_ = lean_st_ref_get(v___y_1242_);
v_env_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_env_1245_);
lean_dec(v___x_1244_);
v___x_1246_ = l_Lean_Environment_header(v_env_1245_);
v_isModule_1247_ = lean_ctor_get_uint8(v___x_1246_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1246_);
if (v_isModule_1247_ == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref(v_env_1245_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
v___x_1248_ = lean_apply_5(v_x_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
return v___x_1248_;
}
else
{
uint8_t v_isExporting_1249_; 
v_isExporting_1249_ = lean_ctor_get_uint8(v_env_1245_, sizeof(void*)*13);
lean_dec_ref(v_env_1245_);
if (v_isExporting_1238_ == 0)
{
if (v_isExporting_1249_ == 0)
{
lean_object* v___x_1316_; 
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
v___x_1316_ = lean_apply_5(v_x_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
return v___x_1316_;
}
else
{
goto v___jp_1250_;
}
}
else
{
if (v_isExporting_1249_ == 0)
{
goto v___jp_1250_;
}
else
{
lean_object* v___x_1317_; 
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
v___x_1317_ = lean_apply_5(v_x_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
return v___x_1317_;
}
}
v___jp_1250_:
{
lean_object* v___x_1251_; lean_object* v_env_1252_; lean_object* v_nextMacroScope_1253_; lean_object* v_ngen_1254_; lean_object* v_auxDeclNGen_1255_; lean_object* v_traceState_1256_; lean_object* v_recordedDeps_1257_; lean_object* v_messages_1258_; lean_object* v_infoState_1259_; lean_object* v_snapshotTasks_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1314_; 
v___x_1251_ = lean_st_ref_take(v___y_1242_);
v_env_1252_ = lean_ctor_get(v___x_1251_, 0);
v_nextMacroScope_1253_ = lean_ctor_get(v___x_1251_, 1);
v_ngen_1254_ = lean_ctor_get(v___x_1251_, 2);
v_auxDeclNGen_1255_ = lean_ctor_get(v___x_1251_, 3);
v_traceState_1256_ = lean_ctor_get(v___x_1251_, 4);
v_recordedDeps_1257_ = lean_ctor_get(v___x_1251_, 6);
v_messages_1258_ = lean_ctor_get(v___x_1251_, 7);
v_infoState_1259_ = lean_ctor_get(v___x_1251_, 8);
v_snapshotTasks_1260_ = lean_ctor_get(v___x_1251_, 9);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1251_, 5);
lean_dec(v_unused_1315_);
v___x_1262_ = v___x_1251_;
v_isShared_1263_ = v_isSharedCheck_1314_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snapshotTasks_1260_);
lean_inc(v_infoState_1259_);
lean_inc(v_messages_1258_);
lean_inc(v_recordedDeps_1257_);
lean_inc(v_traceState_1256_);
lean_inc(v_auxDeclNGen_1255_);
lean_inc(v_ngen_1254_);
lean_inc(v_nextMacroScope_1253_);
lean_inc(v_env_1252_);
lean_dec(v___x_1251_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1314_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1264_ = l_Lean_Environment_setExporting(v_env_1252_, v_isExporting_1238_);
v___x_1265_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 5, v___x_1265_);
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1267_ = v___x_1262_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_nextMacroScope_1253_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_ngen_1254_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_auxDeclNGen_1255_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_traceState_1256_);
lean_ctor_set(v_reuseFailAlloc_1313_, 5, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1313_, 6, v_recordedDeps_1257_);
lean_ctor_set(v_reuseFailAlloc_1313_, 7, v_messages_1258_);
lean_ctor_set(v_reuseFailAlloc_1313_, 8, v_infoState_1259_);
lean_ctor_set(v_reuseFailAlloc_1313_, 9, v_snapshotTasks_1260_);
v___x_1267_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_mctx_1270_; lean_object* v_zetaDeltaFVarIds_1271_; lean_object* v_postponed_1272_; lean_object* v_diag_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1311_; 
v___x_1268_ = lean_st_ref_put(v___y_1242_, v___x_1267_);
v___x_1269_ = lean_st_ref_take(v___y_1240_);
v_mctx_1270_ = lean_ctor_get(v___x_1269_, 0);
v_zetaDeltaFVarIds_1271_ = lean_ctor_get(v___x_1269_, 2);
v_postponed_1272_ = lean_ctor_get(v___x_1269_, 3);
v_diag_1273_ = lean_ctor_get(v___x_1269_, 4);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1269_, 1);
lean_dec(v_unused_1312_);
v___x_1275_ = v___x_1269_;
v_isShared_1276_ = v_isSharedCheck_1311_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_diag_1273_);
lean_inc(v_postponed_1272_);
lean_inc(v_zetaDeltaFVarIds_1271_);
lean_inc(v_mctx_1270_);
lean_dec(v___x_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1311_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__3);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_mctx_1270_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_zetaDeltaFVarIds_1271_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_postponed_1272_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_diag_1273_);
v___x_1279_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v_r_1281_; 
v___x_1280_ = lean_st_ref_put(v___y_1240_, v___x_1279_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
v_r_1281_ = lean_apply_5(v_x_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
if (lean_obj_tag(v_r_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1298_; 
v_a_1282_ = lean_ctor_get(v_r_1281_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_r_1281_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1284_ = v_r_1281_;
v_isShared_1285_ = v_isSharedCheck_1298_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v_r_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1298_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
lean_inc(v_a_1282_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v___x_1288_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1242_, v_isExporting_1249_, v___x_1265_, v___y_1240_, v___x_1277_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___x_1288_, 0);
lean_dec(v_unused_1296_);
v___x_1290_ = v___x_1288_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v___x_1288_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_a_1282_);
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1282_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1299_ = lean_ctor_get(v_r_1281_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v_r_1281_, 1);
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___lam__0(v___y_1242_, v_isExporting_1249_, v___x_1265_, v___y_1240_, v___x_1277_, v___x_1300_);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1309_);
v___x_1303_ = v___x_1301_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v___x_1301_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 1);
lean_ctor_set(v___x_1303_, 0, v_a_1299_);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1299_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1237_ = stack[0].m_obj;
uint8_t v_isExporting_1238_ = stack[1].m_num;
lean_object* v___y_1239_ = stack[2].m_obj;
lean_object* v___y_1240_ = stack[3].m_obj;
lean_object* v___y_1241_ = stack[4].m_obj;
lean_object* v___y_1242_ = stack[5].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1237_, v_isExporting_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg___boxed(lean_object* v_x_1319_, lean_object* v_isExporting_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v_isExporting_boxed_1326_; lean_object* v_res_1327_; 
v_isExporting_boxed_1326_ = lean_unbox(v_isExporting_1320_);
v_res_1327_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1319_, v_isExporting_boxed_1326_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1327_;
}
}
lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(lean_object* v_x_1328_, uint8_t v_when_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
if (v_when_1329_ == 0)
{
lean_object* v___x_1335_; 
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
v___x_1335_ = lean_apply_5(v_x_1328_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, lean_box(0));
return v___x_1335_;
}
else
{
uint8_t v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = 0;
v___x_1337_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1328_, v___x_1336_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1337_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1328_ = stack[0].m_obj;
uint8_t v_when_1329_ = stack[1].m_num;
lean_object* v___y_1330_ = stack[2].m_obj;
lean_object* v___y_1331_ = stack[3].m_obj;
lean_object* v___y_1332_ = stack[4].m_obj;
lean_object* v___y_1333_ = stack[5].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1328_, v_when_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_x_1339_, lean_object* v_when_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_when_boxed_1346_; lean_object* v_res_1347_; 
v_when_boxed_1346_ = lean_unbox(v_when_1340_);
v_res_1347_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1339_, v_when_boxed_1346_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1347_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1350_ = lean_box(1);
v___x_1351_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1352_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
lean_ctor_set(v___x_1353_, 2, v___x_1350_);
return v___x_1353_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1357_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
lean_ctor_set(v___x_1359_, 3, v___x_1358_);
lean_ctor_set(v___x_1359_, 4, v___x_1357_);
lean_ctor_set(v___x_1359_, 5, v___x_1357_);
lean_ctor_set(v___x_1359_, 6, v___x_1357_);
lean_ctor_set(v___x_1359_, 7, v___x_1357_);
lean_ctor_set(v___x_1359_, 8, v___x_1357_);
lean_ctor_set(v___x_1359_, 9, v___x_1357_);
lean_ctor_set(v___x_1359_, 10, v___x_1357_);
lean_ctor_set(v___x_1359_, 11, v___x_1356_);
return v___x_1359_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1361_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
lean_ctor_set(v___x_1361_, 2, v___x_1360_);
lean_ctor_set(v___x_1361_, 3, v___x_1360_);
lean_ctor_set(v___x_1361_, 4, v___x_1360_);
lean_ctor_set(v___x_1361_, 5, v___x_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
lean_ctor_set(v___x_1363_, 2, v___x_1362_);
lean_ctor_set(v___x_1363_, 3, v___x_1362_);
lean_ctor_set(v___x_1363_, 4, v___x_1362_);
return v___x_1363_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(uint8_t v_builtin_1364_, uint8_t v___x_1365_, lean_object* v___x_1366_, lean_object* v___x_1367_, lean_object* v_name_1368_, lean_object* v___x_1369_, lean_object* v_decl_1370_, lean_object* v_stx_1371_, uint8_t v_kind_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; uint64_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1376_ = lean_box(v_builtin_1364_);
v___x_1377_ = lean_box(v___x_1365_);
v___x_1378_ = lean_box(v_kind_1372_);
v___f_1379_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 13, 8);
lean_closure_set(v___f_1379_, 0, v___x_1376_);
lean_closure_set(v___f_1379_, 1, v_decl_1370_);
lean_closure_set(v___f_1379_, 2, v___x_1377_);
lean_closure_set(v___f_1379_, 3, v___x_1366_);
lean_closure_set(v___f_1379_, 4, v___x_1367_);
lean_closure_set(v___f_1379_, 5, v_stx_1371_);
lean_closure_set(v___f_1379_, 6, v___x_1378_);
lean_closure_set(v___f_1379_, 7, v_name_1368_);
v___x_1380_ = 0;
v___x_1381_ = 1;
v___x_1382_ = 0;
v___x_1383_ = 2;
v___x_1384_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1384_, 0, v___x_1380_);
lean_ctor_set_uint8(v___x_1384_, 1, v___x_1380_);
lean_ctor_set_uint8(v___x_1384_, 2, v___x_1380_);
lean_ctor_set_uint8(v___x_1384_, 3, v___x_1380_);
lean_ctor_set_uint8(v___x_1384_, 4, v___x_1380_);
lean_ctor_set_uint8(v___x_1384_, 5, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 6, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 7, v___x_1380_);
lean_ctor_set_uint8(v___x_1384_, 8, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 9, v___x_1381_);
lean_ctor_set_uint8(v___x_1384_, 10, v___x_1382_);
lean_ctor_set_uint8(v___x_1384_, 11, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 12, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 13, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 14, v___x_1383_);
lean_ctor_set_uint8(v___x_1384_, 15, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 16, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 17, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 18, v___x_1365_);
lean_ctor_set_uint8(v___x_1384_, 19, v___x_1380_);
v___x_1385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1384_);
v___x_1386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set_uint64(v___x_1386_, sizeof(void*)*1, v___x_1385_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1389_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1390_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1391_ = lean_box(0);
lean_inc(v___x_1369_);
v___x_1392_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1392_, 0, v___x_1386_);
lean_ctor_set(v___x_1392_, 1, v___x_1369_);
lean_ctor_set(v___x_1392_, 2, v___x_1389_);
lean_ctor_set(v___x_1392_, 3, v___x_1390_);
lean_ctor_set(v___x_1392_, 4, v___x_1391_);
lean_ctor_set(v___x_1392_, 5, v___x_1387_);
lean_ctor_set(v___x_1392_, 6, v___x_1391_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*7, v___x_1380_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*7 + 1, v___x_1380_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*7 + 2, v___x_1380_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*7 + 3, v___x_1365_);
v___x_1393_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1394_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1395_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__5_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1393_);
lean_ctor_set(v___x_1396_, 1, v___x_1394_);
lean_ctor_set(v___x_1396_, 2, v___x_1369_);
lean_ctor_set(v___x_1396_, 3, v___x_1388_);
lean_ctor_set(v___x_1396_, 4, v___x_1395_);
v___x_1397_ = lean_st_mk_ref(v___x_1396_);
v___x_1398_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v___f_1379_, v___x_1365_, v___x_1392_, v___x_1397_, v___y_1373_, v___y_1374_);
lean_dec_ref_known(v___x_1392_, 7);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_st_ref_get(v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v___x_1403_);
if (v_isShared_1402_ == 0)
{
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1399_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_dec(v___x_1397_);
return v___x_1398_;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v_builtin_1364_ = stack[0].m_num;
uint8_t v___x_1365_ = stack[1].m_num;
lean_object* v___x_1366_ = stack[2].m_obj;
lean_object* v___x_1367_ = stack[3].m_obj;
lean_object* v_name_1368_ = stack[4].m_obj;
lean_object* v___x_1369_ = stack[5].m_obj;
lean_object* v_decl_1370_ = stack[6].m_obj;
lean_object* v_stx_1371_ = stack[7].m_obj;
uint8_t v_kind_1372_ = stack[8].m_num;
lean_object* v___y_1373_ = stack[9].m_obj;
lean_object* v___y_1374_ = stack[10].m_obj;
lean_object* v_res_1408_;
v_res_1408_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_1364_, v___x_1365_, v___x_1366_, v___x_1367_, v_name_1368_, v___x_1369_, v_decl_1370_, v_stx_1371_, v_kind_1372_, v___y_1373_, v___y_1374_);
stack->m_obj
 = v_res_1408_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_builtin_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v_name_1413_, lean_object* v___x_1414_, lean_object* v_decl_1415_, lean_object* v_stx_1416_, lean_object* v_kind_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v_builtin_boxed_1421_; uint8_t v___x_12684__boxed_1422_; uint8_t v_kind_boxed_1423_; lean_object* v_res_1424_; 
v_builtin_boxed_1421_ = lean_unbox(v_builtin_1409_);
v___x_12684__boxed_1422_ = lean_unbox(v___x_1410_);
v_kind_boxed_1423_ = lean_unbox(v_kind_1417_);
v_res_1424_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v_builtin_boxed_1421_, v___x_12684__boxed_1422_, v___x_1411_, v___x_1412_, v_name_1413_, v___x_1414_, v_decl_1415_, v_stx_1416_, v_kind_boxed_1423_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1424_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(lean_object* v___x_1432_, uint8_t v_builtin_1433_, lean_object* v_name_1434_){
_start:
{
lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___f_1443_; lean_object* v___y_1445_; 
lean_inc_n(v_name_1434_, 2);
v___f_1436_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1436_, 0, v_name_1434_);
v___x_1437_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__0));
v___x_1438_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe___closed__1));
v___x_1439_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1440_ = 1;
v___x_1441_ = lean_box(v_builtin_1433_);
v___x_1442_ = lean_box(v___x_1440_);
v___f_1443_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1443_, 0, v___x_1441_);
lean_closure_set(v___f_1443_, 1, v___x_1442_);
lean_closure_set(v___f_1443_, 2, v___x_1437_);
lean_closure_set(v___f_1443_, 3, v___x_1438_);
lean_closure_set(v___f_1443_, 4, v_name_1434_);
lean_closure_set(v___f_1443_, 5, v___x_1432_);
if (v_builtin_1433_ == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__3_spec__4_spec__5___closed__0));
v___y_1445_ = v___x_1468_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___y_1445_ = v___x_1469_;
goto v___jp_1444_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v_impl_1450_; lean_object* v___x_1451_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4___closed__2_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
lean_inc_ref(v___y_1445_);
v___x_1447_ = lean_string_append(v___y_1445_, v___x_1446_);
v___x_1448_ = 1;
v___x_1449_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1449_, 0, v___x_1439_);
lean_ctor_set(v___x_1449_, 1, v_name_1434_);
lean_ctor_set(v___x_1449_, 2, v___x_1447_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3, v___x_1448_);
v_impl_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_impl_1450_, 0, v___x_1449_);
lean_ctor_set(v_impl_1450_, 1, v___f_1443_);
lean_ctor_set(v_impl_1450_, 2, v___f_1436_);
lean_inc_ref(v_impl_1450_);
v___x_1451_ = l_Lean_registerBuiltinAttribute(v_impl_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1451_, 0);
lean_dec(v_unused_1459_);
v___x_1453_ = v___x_1451_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v___x_1451_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v_impl_1450_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_impl_1450_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref_known(v_impl_1450_, 3);
v_a_1460_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1451_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1451_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1432_ = stack[0].m_obj;
uint8_t v_builtin_1433_ = stack[1].m_num;
lean_object* v_name_1434_ = stack[2].m_obj;
lean_object* v_res_1470_;
v_res_1470_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1432_, v_builtin_1433_, v_name_1434_);
stack->m_obj
 = v_res_1470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v___x_1471_, lean_object* v_builtin_1472_, lean_object* v_name_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v_builtin_boxed_1475_; lean_object* v_res_1476_; 
v_builtin_boxed_1475_ = lean_unbox(v_builtin_1472_);
v_res_1476_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1471_, v_builtin_boxed_1475_, v_name_1473_);
return v_res_1476_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1484_ = lean_box(1);
v___x_1485_ = 1;
v___x_1486_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1487_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1484_, v___x_1485_, v___x_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref_known(v___x_1487_, 1);
v___x_1488_ = 0;
v___x_1489_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1490_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__4_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_(v___x_1484_, v___x_1488_, v___x_1489_);
return v___x_1490_;
}
else
{
return v___x_1487_;
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1491_;
v_res_1491_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2____boxed(lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_();
return v_res_1493_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v_msg_1495_, v___y_1496_, v___y_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1495_ = stack[1].m_obj;
lean_object* v___y_1496_ = stack[2].m_obj;
lean_object* v___y_1497_ = stack[3].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_1495_, v___y_1496_, v___y_1497_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_msg_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0(v_00_u03b1_1501_, v_msg_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1506_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b4_1507_, lean_object* v_t_1508_, uint64_t v_k_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_t_1508_, v_k_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1508_ = stack[1].m_obj;
uint64_t v_k_1509_ = stack[2].m_num;
lean_object* v_res_1511_;
v_res_1511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(lean_box(0), v_t_1508_, v_k_1509_);
stack->m_obj
 = v_res_1511_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___boxed(lean_object* v_00_u03b4_1512_, lean_object* v_t_1513_, lean_object* v_k_1514_){
_start:
{
uint64_t v_k_boxed_1515_; lean_object* v_res_1516_; 
v_k_boxed_1515_ = lean_unbox_uint64(v_k_1514_);
lean_dec_ref(v_k_1514_);
v_res_1516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2(v_00_u03b4_1512_, v_t_1513_, v_k_boxed_1515_);
lean_dec(v_t_1513_);
return v_res_1516_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1517_, lean_object* v_name_1518_, uint8_t v_kind_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___redArg(v_name_1518_, v_kind_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1518_ = stack[1].m_obj;
uint8_t v_kind_1519_ = stack[2].m_num;
lean_object* v___y_1520_ = stack[3].m_obj;
lean_object* v___y_1521_ = stack[4].m_obj;
lean_object* v___y_1522_ = stack[5].m_obj;
lean_object* v___y_1523_ = stack[6].m_obj;
lean_object* v_res_1526_;
v_res_1526_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(lean_box(0), v_name_1518_, v_kind_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
stack->m_obj
 = v_res_1526_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1527_, lean_object* v_name_1528_, lean_object* v_kind_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_kind_boxed_1535_; lean_object* v_res_1536_; 
v_kind_boxed_1535_ = lean_unbox(v_kind_1529_);
v_res_1536_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4(v_00_u03b1_1527_, v_name_1528_, v_kind_boxed_1535_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1536_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(lean_object* v_00_u03b1_1537_, lean_object* v_x_1538_, uint8_t v_isExporting_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___redArg(v_x_1538_, v_isExporting_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1538_ = stack[1].m_obj;
uint8_t v_isExporting_1539_ = stack[2].m_num;
lean_object* v___y_1540_ = stack[3].m_obj;
lean_object* v___y_1541_ = stack[4].m_obj;
lean_object* v___y_1542_ = stack[5].m_obj;
lean_object* v___y_1543_ = stack[6].m_obj;
lean_object* v_res_1546_;
v_res_1546_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(lean_box(0), v_x_1538_, v_isExporting_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_x_1548_, lean_object* v_isExporting_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_isExporting_boxed_1555_; lean_object* v_res_1556_; 
v_isExporting_boxed_1555_ = lean_unbox(v_isExporting_1549_);
v_res_1556_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_spec__8(v_00_u03b1_1547_, v_x_1548_, v_isExporting_boxed_1555_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1556_;
}
}
lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1557_, lean_object* v_x_1558_, uint8_t v_when_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___redArg(v_x_1558_, v_when_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1558_ = stack[1].m_obj;
uint8_t v_when_1559_ = stack[2].m_num;
lean_object* v___y_1560_ = stack[3].m_obj;
lean_object* v___y_1561_ = stack[4].m_obj;
lean_object* v___y_1562_ = stack[5].m_obj;
lean_object* v___y_1563_ = stack[6].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(lean_box(0), v_x_1558_, v_when_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
stack->m_obj
 = v_res_1566_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_x_1568_, lean_object* v_when_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_when_boxed_1575_; lean_object* v_res_1576_; 
v_when_boxed_1575_ = lean_unbox(v_when_1569_);
v_res_1576_ = l_Lean_withoutExporting___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__5(v_00_u03b1_1567_, v_x_1568_, v_when_boxed_1575_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1576_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1577_, lean_object* v_msg_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v_msg_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1578_ = stack[1].m_obj;
lean_object* v___y_1579_ = stack[2].m_obj;
lean_object* v___y_1580_ = stack[3].m_obj;
lean_object* v___y_1581_ = stack[4].m_obj;
lean_object* v___y_1582_ = stack[5].m_obj;
lean_object* v_res_1585_;
v_res_1585_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(lean_box(0), v_msg_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
stack->m_obj
 = v_res_1585_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1586_, lean_object* v_msg_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1586_, v_msg_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
if (lean_obj_tag(v_a_1594_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_array_to_list(v_a_1595_);
return v___x_1596_;
}
else
{
lean_object* v_head_1597_; lean_object* v_tail_1598_; lean_object* v___x_1599_; 
v_head_1597_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_head_1597_);
v_tail_1598_ = lean_ctor_get(v_a_1594_, 1);
lean_inc(v_tail_1598_);
lean_dec_ref_known(v_a_1594_, 2);
v___x_1599_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1595_, v_head_1597_);
v_a_1594_ = v_tail_1598_;
v_a_1595_ = v___x_1599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson(lean_object* v_x_1605_){
_start:
{
uint64_t v_hash_1606_; lean_object* v_pos_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_hash_1606_ = lean_ctor_get_uint64(v_x_1605_, sizeof(void*)*1);
v_pos_1607_ = lean_ctor_get(v_x_1605_, 0);
lean_inc_ref(v_pos_1607_);
lean_dec_ref(v_x_1605_);
v___x_1608_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
v___x_1609_ = lean_uint64_to_nat(v_hash_1606_);
v___x_1610_ = l_Lean_bignumToJson(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1615_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_1607_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1612_);
v___x_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1612_);
v___x_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1613_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1621_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1619_, v___x_1620_);
v___x_1622_ = l_Lean_Json_mkObj(v___x_1621_);
lean_dec(v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(lean_object* v_j_1625_, lean_object* v_k_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = l_Lean_Json_getObjValD(v_j_1625_, v_k_1626_);
v___x_1628_ = l_Lean_UInt64_fromJson_x3f(v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0___boxed(lean_object* v_j_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_j_1629_, v_k_1630_);
lean_dec_ref(v_k_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(lean_object* v_j_1632_, lean_object* v_k_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = l_Lean_Json_getObjValD(v_j_1632_, v_k_1633_);
v___x_1635_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1___boxed(lean_object* v_j_1636_, lean_object* v_k_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_j_1636_, v_k_1637_);
lean_dec_ref(v_k_1637_);
return v_res_1638_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = 1;
v___x_1645_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__1));
v___x_1646_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1648_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__2);
v___x_1649_ = lean_string_append(v___x_1648_, v___x_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = 1;
v___x_1653_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__4));
v___x_1654_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1653_, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__5);
v___x_1656_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1657_ = lean_string_append(v___x_1656_, v___x_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1660_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__6);
v___x_1661_ = lean_string_append(v___x_1660_, v___x_1659_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = 1;
v___x_1665_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__9));
v___x_1666_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1665_, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__10);
v___x_1668_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__3);
v___x_1669_ = lean_string_append(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1671_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__11);
v___x_1672_ = lean_string_append(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(lean_object* v_json_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__0));
lean_inc(v_json_1673_);
v___x_1675_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__0(v_json_1673_, v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_json_1673_);
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1680_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__8);
v___x_1681_ = lean_string_append(v___x_1680_, v_a_1676_);
lean_dec(v_a_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_json_1673_);
v_a_1686_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1675_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1675_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 0);
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_a_1694_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1695_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__1));
v___x_1696_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson_spec__1(v_json_1673_, v___x_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1694_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1706_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1706_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1701_ = lean_obj_once(&l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12, &l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12_once, _init_l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__12);
v___x_1702_ = lean_string_append(v___x_1701_, v_a_1697_);
lean_dec(v_a_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1702_);
v___x_1704_ = v___x_1699_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_a_1694_);
v_a_1707_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1696_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1696_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 0);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1724_; 
v_a_1715_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1717_ = v___x_1696_;
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1696_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; uint64_t v___x_1720_; lean_object* v___x_1722_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1719_, 0, v_a_1715_);
v___x_1720_ = lean_unbox_uint64(v_a_1694_);
lean_dec(v_a_1694_);
lean_ctor_set_uint64(v___x_1719_, sizeof(void*)*1, v___x_1720_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1722_ = v___x_1717_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1719_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonWidgetSource_toJson(lean_object* v_x_1730_){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1731_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1732_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_x_1730_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v___x_1734_);
v___x_1737_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_1738_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_1736_, v___x_1737_);
v___x_1739_ = l_Lean_Json_mkObj(v___x_1738_);
lean_dec(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(lean_object* v_j_1742_, lean_object* v_k_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = l_Lean_Json_getObjValD(v_j_1742_, v_k_1743_);
v___x_1745_ = l_Lean_Json_getStr_x3f(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0___boxed(lean_object* v_j_1746_, lean_object* v_k_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_j_1746_, v_k_1747_);
lean_dec_ref(v_k_1747_);
return v_res_1748_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = 1;
v___x_1755_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__1));
v___x_1756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_1758_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__2);
v___x_1759_ = lean_string_append(v___x_1758_, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = 1;
v___x_1763_ = ((lean_object*)(l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__4));
v___x_1764_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1763_, v___x_1762_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__5);
v___x_1766_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__3);
v___x_1767_ = lean_string_append(v___x_1766_, v___x_1765_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_1769_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__6);
v___x_1770_ = lean_string_append(v___x_1769_, v___x_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonWidgetSource_fromJson(lean_object* v_json_1771_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_Widget_instToJsonWidgetSource_toJson___closed__0));
v___x_1773_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_1771_, v___x_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1783_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_obj_once(&l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7, &l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonWidgetSource_fromJson___closed__7);
v___x_1779_ = lean_string_append(v___x_1778_, v_a_1774_);
lean_dec(v_a_1774_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1773_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1773_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 0);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1773_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1773_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(lean_object* v___y_1802_){
_start:
{
lean_object* v_doc_1804_; lean_object* v___x_1805_; 
v_doc_1804_ = lean_ctor_get(v___y_1802_, 1);
lean_inc_ref(v_doc_1804_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_doc_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1802_ = stack[0].m_obj;
lean_object* v_res_1806_;
v_res_1806_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1802_);
stack->m_obj
 = v_res_1806_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0___boxed(lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v___y_1807_);
lean_dec_ref(v___y_1807_);
return v_res_1809_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(uint64_t v_k_1810_, lean_object* v_t_1811_){
_start:
{
if (lean_obj_tag(v_t_1811_) == 0)
{
lean_object* v_k_1812_; lean_object* v_l_1813_; lean_object* v_r_1814_; uint64_t v___x_1815_; uint8_t v___x_1816_; 
v_k_1812_ = lean_ctor_get(v_t_1811_, 1);
v_l_1813_ = lean_ctor_get(v_t_1811_, 3);
v_r_1814_ = lean_ctor_get(v_t_1811_, 4);
v___x_1815_ = lean_unbox_uint64(v_k_1812_);
v___x_1816_ = lean_uint64_dec_lt(v_k_1810_, v___x_1815_);
if (v___x_1816_ == 0)
{
uint64_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = lean_unbox_uint64(v_k_1812_);
v___x_1818_ = lean_uint64_dec_eq(v_k_1810_, v___x_1817_);
if (v___x_1818_ == 0)
{
v_t_1811_ = v_r_1814_;
goto _start;
}
else
{
return v___x_1818_;
}
}
else
{
v_t_1811_ = v_l_1813_;
goto _start;
}
}
else
{
uint8_t v___x_1821_; 
v___x_1821_ = 0;
return v___x_1821_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_1810_ = stack[0].m_num;
lean_object* v_t_1811_ = stack[1].m_obj;
uint8_t v_res_1822_;
v_res_1822_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1810_, v_t_1811_);
stack->m_num = v_res_1822_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg___boxed(lean_object* v_k_1823_, lean_object* v_t_1824_){
_start:
{
uint64_t v_k_boxed_1825_; uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_k_boxed_1825_ = lean_unbox_uint64(v_k_1823_);
lean_dec_ref(v_k_1823_);
v_res_1826_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_boxed_1825_, v_t_1824_);
lean_dec(v_t_1824_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
uint8_t l_Lean_Widget_getWidgetSource___lam__0(lean_object* v___x_1828_, uint64_t v_hash_1829_, lean_object* v_s_1830_){
_start:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1830_);
v___x_1832_ = lean_nat_dec_le(v___x_1828_, v___x_1831_);
lean_dec(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v_toEnvExtension_1834_; lean_object* v_asyncMode_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1833_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1834_ = lean_ctor_get(v___x_1833_, 0);
v_asyncMode_1835_ = lean_ctor_get(v_toEnvExtension_1834_, 2);
v___x_1836_ = lean_box(1);
v___x_1837_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_1830_);
v___x_1838_ = lean_box(0);
v___x_1839_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1836_, v___x_1833_, v___x_1837_, v_asyncMode_1835_, v___x_1838_);
v___x_1840_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_hash_1829_, v___x_1839_);
lean_dec(v___x_1839_);
return v___x_1840_;
}
else
{
return v___x_1832_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgetSource___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1828_ = stack[0].m_obj;
uint64_t v_hash_1829_ = stack[1].m_num;
lean_object* v_s_1830_ = stack[2].m_obj;
uint8_t v_res_1841_;
v_res_1841_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1828_, v_hash_1829_, v_s_1830_);
stack->m_num = v_res_1841_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__0___boxed(lean_object* v___x_1842_, lean_object* v_hash_1843_, lean_object* v_s_1844_){
_start:
{
uint64_t v_hash_boxed_1845_; uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_hash_boxed_1845_ = lean_unbox_uint64(v_hash_1843_);
lean_dec_ref(v_hash_1843_);
v_res_1846_ = l_Lean_Widget_getWidgetSource___lam__0(v___x_1842_, v_hash_boxed_1845_, v_s_1844_);
lean_dec_ref(v_s_1844_);
lean_dec(v___x_1842_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
lean_object* l_Lean_Widget_getWidgetSource___lam__1(lean_object* v___x_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1848_);
return v___x_1851_;
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgetSource___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1848_ = stack[0].m_obj;
lean_object* v___y_1849_ = stack[1].m_obj;
lean_object* v_res_1852_;
v_res_1852_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1848_, v___y_1849_);
stack->m_obj
 = v_res_1852_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__1___boxed(lean_object* v___x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Widget_getWidgetSource___lam__1(v___x_1853_, v___y_1854_);
lean_dec_ref(v___y_1854_);
return v_res_1856_;
}
}
lean_object* l_Lean_Widget_getWidgetSource___lam__2(lean_object* v_snd_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_snd_1857_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1876_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1876_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1876_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_javascript_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v_javascript_1871_ = lean_ctor_get(v_a_1867_, 0);
lean_inc_ref(v_javascript_1871_);
lean_dec(v_a_1867_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_javascript_1871_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1866_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1866_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgetSource___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1857_ = stack[0].m_obj;
lean_object* v___y_1858_ = stack[1].m_obj;
lean_object* v___y_1859_ = stack[2].m_obj;
lean_object* v___y_1860_ = stack[3].m_obj;
lean_object* v___y_1861_ = stack[4].m_obj;
lean_object* v___y_1862_ = stack[5].m_obj;
lean_object* v___y_1863_ = stack[6].m_obj;
lean_object* v___y_1864_ = stack[7].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__2___boxed(lean_object* v_snd_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Widget_getWidgetSource___lam__2(v_snd_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1895_;
}
}
lean_object* l_Lean_Widget_getWidgetSource___lam__3(uint64_t v_hash_1896_, lean_object* v___x_1897_, lean_object* v_snap_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; lean_object* v_toEnvExtension_1902_; lean_object* v_asyncMode_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1901_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_1902_ = lean_ctor_get(v___x_1901_, 0);
v_asyncMode_1903_ = lean_ctor_get(v_toEnvExtension_1902_, 2);
v___x_1904_ = lean_box(1);
v___x_1905_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1898_);
v___x_1906_ = lean_box(0);
v___x_1907_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1904_, v___x_1901_, v___x_1905_, v_asyncMode_1903_, v___x_1906_);
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1907_, v_hash_1896_);
lean_dec(v___x_1907_);
if (lean_obj_tag(v___x_1908_) == 1)
{
lean_object* v_val_1909_; lean_object* v_snd_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; 
lean_dec_ref(v___x_1897_);
v_val_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v_snd_1910_ = lean_ctor_get(v_val_1909_, 1);
lean_inc(v_snd_1910_);
lean_dec(v_val_1909_);
v___f_1911_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__2___boxed), 9, 1);
lean_closure_set(v___f_1911_, 0, v_snd_1910_);
v___x_1912_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1898_, v___f_1911_, v___y_1899_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; 
lean_dec(v___x_1908_);
lean_dec_ref(v_snap_1898_);
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1897_);
return v___x_1913_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgetSource___lam__3_0interp(lean_interpreter_value* stack)
{
uint64_t v_hash_1896_ = stack[0].m_num;
lean_object* v___x_1897_ = stack[1].m_obj;
lean_object* v_snap_1898_ = stack[2].m_obj;
lean_object* v___y_1899_ = stack[3].m_obj;
lean_object* v_res_1914_;
v_res_1914_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_1896_, v___x_1897_, v_snap_1898_, v___y_1899_);
stack->m_obj
 = v_res_1914_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___lam__3___boxed(lean_object* v_hash_1915_, lean_object* v___x_1916_, lean_object* v_snap_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
uint64_t v_hash_boxed_1920_; lean_object* v_res_1921_; 
v_hash_boxed_1920_ = lean_unbox_uint64(v_hash_1915_);
lean_dec_ref(v_hash_1915_);
v_res_1921_ = l_Lean_Widget_getWidgetSource___lam__3(v_hash_boxed_1920_, v___x_1916_, v_snap_1917_, v___y_1918_);
lean_dec_ref(v___y_1918_);
return v_res_1921_;
}
}
lean_object* l_Lean_Widget_getWidgetSource(lean_object* v_args_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; uint64_t v_hash_1929_; lean_object* v_pos_1930_; lean_object* v___x_1931_; 
v___x_1927_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_1928_ = lean_st_ref_get(v___x_1927_);
v_hash_1929_ = lean_ctor_get_uint64(v_args_1924_, sizeof(void*)*1);
v_pos_1930_ = lean_ctor_get(v_args_1924_, 0);
lean_inc_ref(v_pos_1930_);
lean_dec_ref(v_args_1924_);
v___x_1931_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_1928_, v_hash_1929_);
lean_dec(v___x_1928_);
if (lean_obj_tag(v___x_1931_) == 1)
{
lean_object* v_val_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_pos_1930_);
v_val_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_val_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_snd_1936_; lean_object* v_javascript_1937_; lean_object* v___x_1939_; 
v_snd_1936_ = lean_ctor_get(v_val_1932_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_val_1932_);
v_javascript_1937_ = lean_ctor_get(v_snd_1936_, 0);
lean_inc_ref(v_javascript_1937_);
lean_dec(v_snd_1936_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_javascript_1937_);
v___x_1939_ = v___x_1934_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_javascript_1937_);
v___x_1939_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_task_pure(v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
}
}
else
{
lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v_toEditableDocumentCore_1946_; lean_object* v_meta_1947_; lean_object* v_text_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; 
lean_dec(v___x_1931_);
v___x_1944_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_1925_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v_toEditableDocumentCore_1946_ = lean_ctor_get(v_a_1945_, 0);
v_meta_1947_ = lean_ctor_get(v_toEditableDocumentCore_1946_, 0);
v_text_1948_ = lean_ctor_get(v_meta_1947_, 3);
v___x_1949_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1948_, v_pos_1930_);
v___x_1950_ = lean_box_uint64(v_hash_1929_);
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1951_, 0, v___x_1949_);
lean_closure_set(v___f_1951_, 1, v___x_1950_);
v___x_1952_ = 3;
v___x_1953_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_1954_ = lean_uint64_to_nat(v_hash_1929_);
v___x_1955_ = l_Nat_reprFast(v___x_1954_);
v___x_1956_ = lean_string_append(v___x_1953_, v___x_1955_);
lean_dec_ref(v___x_1955_);
v___x_1957_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_1958_ = lean_string_append(v___x_1956_, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*1, v___x_1952_);
lean_inc_ref(v___x_1959_);
v___f_1960_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1960_, 0, v___x_1959_);
v___x_1961_ = lean_box_uint64(v_hash_1929_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgetSource___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1962_, 0, v___x_1961_);
lean_closure_set(v___f_1962_, 1, v___x_1959_);
v___x_1963_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1945_, v___f_1951_, v___f_1960_, v___f_1962_, v_a_1925_);
return v___x_1963_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgetSource_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1924_ = stack[0].m_obj;
lean_object* v_a_1925_ = stack[1].m_obj;
lean_object* v_res_1964_;
v_res_1964_ = l_Lean_Widget_getWidgetSource(v_args_1924_, v_a_1925_);
stack->m_obj
 = v_res_1964_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgetSource___boxed(lean_object* v_args_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Widget_getWidgetSource(v_args_1965_, v_a_1966_);
lean_dec_ref(v_a_1966_);
return v_res_1968_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_object* v_00_u03b2_1969_, uint64_t v_k_1970_, lean_object* v_t_1971_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___redArg(v_k_1970_, v_t_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_1970_ = stack[1].m_num;
lean_object* v_t_1971_ = stack[2].m_obj;
uint8_t v_res_1973_;
v_res_1973_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(lean_box(0), v_k_1970_, v_t_1971_);
stack->m_num = v_res_1973_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1___boxed(lean_object* v_00_u03b2_1974_, lean_object* v_k_1975_, lean_object* v_t_1976_){
_start:
{
uint64_t v_k_boxed_1977_; uint8_t v_res_1978_; lean_object* v_r_1979_; 
v_k_boxed_1977_ = lean_unbox_uint64(v_k_1975_);
lean_dec_ref(v_k_1975_);
v_res_1978_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_getWidgetSource_spec__1(v_00_u03b2_1974_, v_k_boxed_1977_, v_t_1976_);
lean_dec(v_t_1976_);
v_r_1979_ = lean_box(v_res_1978_);
return v_r_1979_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_1980_, lean_object* v_i_1981_, lean_object* v_k_1982_){
_start:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = lean_array_get_size(v_keys_1980_);
v___x_1984_ = lean_nat_dec_lt(v_i_1981_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_dec(v_i_1981_);
return v___x_1984_;
}
else
{
lean_object* v_k_x27_1985_; uint8_t v___x_1986_; 
v_k_x27_1985_ = lean_array_fget_borrowed(v_keys_1980_, v_i_1981_);
v___x_1986_ = lean_name_eq(v_k_1982_, v_k_x27_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_add(v_i_1981_, v___x_1987_);
lean_dec(v_i_1981_);
v_i_1981_ = v___x_1988_;
goto _start;
}
else
{
lean_dec(v_i_1981_);
return v___x_1984_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1980_ = stack[0].m_obj;
lean_object* v_i_1981_ = stack[1].m_obj;
lean_object* v_k_1982_ = stack[2].m_obj;
uint8_t v_res_1990_;
v_res_1990_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1980_, v_i_1981_, v_k_1982_);
stack->m_num = v_res_1990_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_1991_, lean_object* v_i_1992_, lean_object* v_k_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1991_, v_i_1992_, v_k_1993_);
lean_dec(v_k_1993_);
lean_dec_ref(v_keys_1991_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_1996_, size_t v_x_1997_, lean_object* v_x_1998_){
_start:
{
if (lean_obj_tag(v_x_1996_) == 0)
{
lean_object* v_es_1999_; lean_object* v___x_2000_; size_t v___x_2001_; size_t v___x_2002_; lean_object* v_j_2003_; lean_object* v___x_2004_; 
v_es_1999_ = lean_ctor_get(v_x_1996_, 0);
v___x_2000_ = lean_box(2);
v___x_2001_ = ((size_t)31ULL);
v___x_2002_ = lean_usize_land(v_x_1997_, v___x_2001_);
v_j_2003_ = lean_usize_to_nat(v___x_2002_);
v___x_2004_ = lean_array_get_borrowed(v___x_2000_, v_es_1999_, v_j_2003_);
lean_dec(v_j_2003_);
switch(lean_obj_tag(v___x_2004_))
{
case 0:
{
lean_object* v_key_2005_; uint8_t v___x_2006_; 
v_key_2005_ = lean_ctor_get(v___x_2004_, 0);
v___x_2006_ = lean_name_eq(v_x_1998_, v_key_2005_);
return v___x_2006_;
}
case 1:
{
lean_object* v_node_2007_; size_t v___x_2008_; size_t v___x_2009_; 
v_node_2007_ = lean_ctor_get(v___x_2004_, 0);
v___x_2008_ = ((size_t)5ULL);
v___x_2009_ = lean_usize_shift_right(v_x_1997_, v___x_2008_);
v_x_1996_ = v_node_2007_;
v_x_1997_ = v___x_2009_;
goto _start;
}
default: 
{
uint8_t v___x_2011_; 
v___x_2011_ = 0;
return v___x_2011_;
}
}
}
else
{
lean_object* v_ks_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_ks_2012_ = lean_ctor_get(v_x_1996_, 0);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_2012_, v___x_2013_, v_x_1998_);
return v___x_2014_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1996_ = stack[0].m_obj;
size_t v_x_1997_ = stack[1].m_num;
lean_object* v_x_1998_ = stack[2].m_obj;
uint8_t v_res_2015_;
v_res_2015_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1996_, v_x_1997_, v_x_1998_);
stack->m_num = v_res_2015_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_){
_start:
{
size_t v_x_1068__boxed_2019_; uint8_t v_res_2020_; lean_object* v_r_2021_; 
v_x_1068__boxed_2019_ = lean_unbox_usize(v_x_2017_);
lean_dec(v_x_2017_);
v_res_2020_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2016_, v_x_1068__boxed_2019_, v_x_2018_);
lean_dec(v_x_2018_);
lean_dec_ref(v_x_2016_);
v_r_2021_ = lean_box(v_res_2020_);
return v_r_2021_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
uint64_t v___y_2025_; 
if (lean_obj_tag(v_x_2023_) == 0)
{
uint64_t v___x_2028_; 
v___x_2028_ = 1723ULL;
v___y_2025_ = v___x_2028_;
goto v___jp_2024_;
}
else
{
uint64_t v_hash_2029_; 
v_hash_2029_ = lean_ctor_get_uint64(v_x_2023_, sizeof(void*)*2);
v___y_2025_ = v_hash_2029_;
goto v___jp_2024_;
}
v___jp_2024_:
{
size_t v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = lean_uint64_to_usize(v___y_2025_);
v___x_2027_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2022_, v___x_2026_, v_x_2023_);
return v___x_2027_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2022_ = stack[0].m_obj;
lean_object* v_x_2023_ = stack[1].m_obj;
uint8_t v_res_2030_;
v_res_2030_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2022_, v_x_2023_);
stack->m_num = v_res_2030_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_res_2033_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2031_, v_x_2032_);
lean_dec(v_x_2032_);
lean_dec_ref(v_x_2031_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
lean_object* v_ks_2039_; lean_object* v_vs_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2064_; 
v_ks_2039_ = lean_ctor_get(v_x_2035_, 0);
v_vs_2040_ = lean_ctor_get(v_x_2035_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_x_2035_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2042_ = v_x_2035_;
v_isShared_2043_ = v_isSharedCheck_2064_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_vs_2040_);
lean_inc(v_ks_2039_);
lean_dec(v_x_2035_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2064_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = lean_array_get_size(v_ks_2039_);
v___x_2045_ = lean_nat_dec_lt(v_x_2036_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
lean_dec(v_x_2036_);
v___x_2046_ = lean_array_push(v_ks_2039_, v_x_2037_);
v___x_2047_ = lean_array_push(v_vs_2040_, v_x_2038_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___x_2047_);
lean_ctor_set(v___x_2042_, 0, v___x_2046_);
v___x_2049_ = v___x_2042_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
else
{
lean_object* v_k_x27_2051_; uint8_t v___x_2052_; 
v_k_x27_2051_ = lean_array_fget_borrowed(v_ks_2039_, v_x_2036_);
v___x_2052_ = lean_name_eq(v_x_2037_, v_k_x27_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2054_; 
if (v_isShared_2043_ == 0)
{
v___x_2054_ = v___x_2042_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_ks_2039_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_vs_2040_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_add(v_x_2036_, v___x_2055_);
lean_dec(v_x_2036_);
v_x_2035_ = v___x_2054_;
v_x_2036_ = v___x_2056_;
goto _start;
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2059_ = lean_array_fset(v_ks_2039_, v_x_2036_, v_x_2037_);
v___x_2060_ = lean_array_fset(v_vs_2040_, v_x_2036_, v_x_2038_);
lean_dec(v_x_2036_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___x_2060_);
lean_ctor_set(v___x_2042_, 0, v___x_2059_);
v___x_2062_ = v___x_2042_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_n_2065_, lean_object* v_k_2066_, lean_object* v_v_2067_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_n_2065_, v___x_2068_, v_k_2066_, v_v_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2070_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_x_2071_, size_t v_x_2072_, size_t v_x_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
if (lean_obj_tag(v_x_2071_) == 0)
{
lean_object* v_es_2076_; size_t v___x_2077_; size_t v___x_2078_; lean_object* v_j_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_es_2076_ = lean_ctor_get(v_x_2071_, 0);
v___x_2077_ = ((size_t)31ULL);
v___x_2078_ = lean_usize_land(v_x_2072_, v___x_2077_);
v_j_2079_ = lean_usize_to_nat(v___x_2078_);
v___x_2080_ = lean_array_get_size(v_es_2076_);
v___x_2081_ = lean_nat_dec_lt(v_j_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_dec(v_j_2079_);
lean_dec(v_x_2075_);
lean_dec(v_x_2074_);
return v_x_2071_;
}
else
{
lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2120_; 
lean_inc_ref(v_es_2076_);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_x_2071_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_x_2071_, 0);
lean_dec(v_unused_2121_);
v___x_2083_ = v_x_2071_;
v_isShared_2084_ = v_isSharedCheck_2120_;
goto v_resetjp_2082_;
}
else
{
lean_dec(v_x_2071_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2120_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_v_2085_; lean_object* v___x_2086_; lean_object* v_xs_x27_2087_; lean_object* v___y_2089_; 
v_v_2085_ = lean_array_fget(v_es_2076_, v_j_2079_);
v___x_2086_ = lean_box(0);
v_xs_x27_2087_ = lean_array_fset(v_es_2076_, v_j_2079_, v___x_2086_);
switch(lean_obj_tag(v_v_2085_))
{
case 0:
{
lean_object* v_key_2094_; lean_object* v_val_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2105_; 
v_key_2094_ = lean_ctor_get(v_v_2085_, 0);
v_val_2095_ = lean_ctor_get(v_v_2085_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_v_2085_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2097_ = v_v_2085_;
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_val_2095_);
lean_inc(v_key_2094_);
lean_dec(v_v_2085_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_name_eq(v_x_2074_, v_key_2094_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_del_object(v___x_2097_);
v___x_2100_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2094_, v_val_2095_, v_x_2074_, v_x_2075_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
v___y_2089_ = v___x_2101_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2103_; 
lean_dec(v_val_2095_);
lean_dec(v_key_2094_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v_x_2075_);
lean_ctor_set(v___x_2097_, 0, v_x_2074_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_x_2074_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_x_2075_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
v___y_2089_ = v___x_2103_;
goto v___jp_2088_;
}
}
}
}
case 1:
{
lean_object* v_node_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2118_; 
v_node_2106_ = lean_ctor_get(v_v_2085_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_v_2085_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2108_ = v_v_2085_;
v_isShared_2109_ = v_isSharedCheck_2118_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_node_2106_);
lean_dec(v_v_2085_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2118_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
size_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2110_ = ((size_t)5ULL);
v___x_2111_ = lean_usize_shift_right(v_x_2072_, v___x_2110_);
v___x_2112_ = ((size_t)1ULL);
v___x_2113_ = lean_usize_add(v_x_2073_, v___x_2112_);
v___x_2114_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_node_2106_, v___x_2111_, v___x_2113_, v_x_2074_, v_x_2075_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2114_);
v___x_2116_ = v___x_2108_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
v___y_2089_ = v___x_2116_;
goto v___jp_2088_;
}
}
}
default: 
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_x_2074_);
lean_ctor_set(v___x_2119_, 1, v_x_2075_);
v___y_2089_ = v___x_2119_;
goto v___jp_2088_;
}
}
v___jp_2088_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_array_fset(v_xs_x27_2087_, v_j_2079_, v___y_2089_);
lean_dec(v_j_2079_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2090_);
v___x_2092_ = v___x_2083_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_object* v_ks_2122_; lean_object* v_vs_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2141_; 
v_ks_2122_ = lean_ctor_get(v_x_2071_, 0);
v_vs_2123_ = lean_ctor_get(v_x_2071_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_x_2071_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2125_ = v_x_2071_;
v_isShared_2126_ = v_isSharedCheck_2141_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_vs_2123_);
lean_inc(v_ks_2122_);
lean_dec(v_x_2071_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2141_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_ks_2122_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_vs_2123_);
v___x_2128_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v_newNode_2129_; size_t v___x_2130_; uint8_t v___x_2131_; 
v_newNode_2129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v___x_2128_, v_x_2074_, v_x_2075_);
v___x_2130_ = ((size_t)7ULL);
v___x_2131_ = lean_usize_dec_le(v___x_2130_, v_x_2073_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2129_);
v___x_2133_ = lean_unsigned_to_nat(4u);
v___x_2134_ = lean_nat_dec_lt(v___x_2132_, v___x_2133_);
lean_dec(v___x_2132_);
if (v___x_2134_ == 0)
{
lean_object* v_ks_2135_; lean_object* v_vs_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_ks_2135_ = lean_ctor_get(v_newNode_2129_, 0);
lean_inc_ref(v_ks_2135_);
v_vs_2136_ = lean_ctor_get(v_newNode_2129_, 1);
lean_inc_ref(v_vs_2136_);
lean_dec_ref(v_newNode_2129_);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___closed__0);
v___x_2139_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_x_2073_, v_ks_2135_, v_vs_2136_, v___x_2137_, v___x_2138_);
lean_dec_ref(v_vs_2136_);
lean_dec_ref(v_ks_2135_);
return v___x_2139_;
}
else
{
return v_newNode_2129_;
}
}
else
{
return v_newNode_2129_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2071_ = stack[0].m_obj;
size_t v_x_2072_ = stack[1].m_num;
size_t v_x_2073_ = stack[2].m_num;
lean_object* v_x_2074_ = stack[3].m_obj;
lean_object* v_x_2075_ = stack[4].m_obj;
lean_object* v_res_2142_;
v_res_2142_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2071_, v_x_2072_, v_x_2073_, v_x_2074_, v_x_2075_);
stack->m_obj
 = v_res_2142_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(size_t v_depth_2143_, lean_object* v_keys_2144_, lean_object* v_vals_2145_, lean_object* v_i_2146_, lean_object* v_entries_2147_){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_array_get_size(v_keys_2144_);
v___x_2149_ = lean_nat_dec_lt(v_i_2146_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_dec(v_i_2146_);
return v_entries_2147_;
}
else
{
lean_object* v_k_2150_; lean_object* v_v_2151_; uint64_t v___y_2153_; 
v_k_2150_ = lean_array_fget_borrowed(v_keys_2144_, v_i_2146_);
v_v_2151_ = lean_array_fget_borrowed(v_vals_2145_, v_i_2146_);
if (lean_obj_tag(v_k_2150_) == 0)
{
uint64_t v___x_2164_; 
v___x_2164_ = 1723ULL;
v___y_2153_ = v___x_2164_;
goto v___jp_2152_;
}
else
{
uint64_t v_hash_2165_; 
v_hash_2165_ = lean_ctor_get_uint64(v_k_2150_, sizeof(void*)*2);
v___y_2153_ = v_hash_2165_;
goto v___jp_2152_;
}
v___jp_2152_:
{
size_t v_h_2154_; size_t v___x_2155_; lean_object* v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; size_t v_h_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_h_2154_ = lean_uint64_to_usize(v___y_2153_);
v___x_2155_ = ((size_t)5ULL);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_sub(v_depth_2143_, v___x_2157_);
v___x_2159_ = lean_usize_mul(v___x_2155_, v___x_2158_);
v_h_2160_ = lean_usize_shift_right(v_h_2154_, v___x_2159_);
v___x_2161_ = lean_nat_add(v_i_2146_, v___x_2156_);
lean_dec(v_i_2146_);
lean_inc(v_v_2151_);
lean_inc(v_k_2150_);
v___x_2162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_entries_2147_, v_h_2160_, v_depth_2143_, v_k_2150_, v_v_2151_);
v_i_2146_ = v___x_2161_;
v_entries_2147_ = v___x_2162_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2143_ = stack[0].m_num;
lean_object* v_keys_2144_ = stack[1].m_obj;
lean_object* v_vals_2145_ = stack[2].m_obj;
lean_object* v_i_2146_ = stack[3].m_obj;
lean_object* v_entries_2147_ = stack[4].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2143_, v_keys_2144_, v_vals_2145_, v_i_2146_, v_entries_2147_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_depth_2167_, lean_object* v_keys_2168_, lean_object* v_vals_2169_, lean_object* v_i_2170_, lean_object* v_entries_2171_){
_start:
{
size_t v_depth_boxed_2172_; lean_object* v_res_2173_; 
v_depth_boxed_2172_ = lean_unbox_usize(v_depth_2167_);
lean_dec(v_depth_2167_);
v_res_2173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_boxed_2172_, v_keys_2168_, v_vals_2169_, v_i_2170_, v_entries_2171_);
lean_dec_ref(v_vals_2169_);
lean_dec_ref(v_keys_2168_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
size_t v_x_1264__boxed_2179_; size_t v_x_1265__boxed_2180_; lean_object* v_res_2181_; 
v_x_1264__boxed_2179_ = lean_unbox_usize(v_x_2175_);
lean_dec(v_x_2175_);
v_x_1265__boxed_2180_ = lean_unbox_usize(v_x_2176_);
lean_dec(v_x_2176_);
v_res_2181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2174_, v_x_1264__boxed_2179_, v_x_1265__boxed_2180_, v_x_2177_, v_x_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
uint64_t v___y_2186_; 
if (lean_obj_tag(v_x_2183_) == 0)
{
uint64_t v___x_2190_; 
v___x_2190_ = 1723ULL;
v___y_2186_ = v___x_2190_;
goto v___jp_2185_;
}
else
{
uint64_t v_hash_2191_; 
v_hash_2191_ = lean_ctor_get_uint64(v_x_2183_, sizeof(void*)*2);
v___y_2186_ = v_hash_2191_;
goto v___jp_2185_;
}
v___jp_2185_:
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_uint64_to_usize(v___y_2186_);
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2182_, v___x_2187_, v___x_2188_, v_x_2183_, v_x_2184_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v___y_2192_){
_start:
{
lean_inc(v___y_2192_);
return v___y_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__0(v___y_2193_);
lean_dec(v___y_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1(lean_object* v_expireTime_2195_, lean_object* v_x_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_x_2196_);
lean_ctor_set(v___x_2197_, 1, v_expireTime_2195_);
return v___x_2197_;
}
}
lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(lean_object* v_val_2198_, lean_object* v___f_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_){
_start:
{
if (lean_obj_tag(v_x_2200_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v___f_2199_);
v_a_2203_ = lean_ctor_get(v_x_2200_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_x_2200_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v_x_2200_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v_x_2200_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set_tag(v___x_2205_, 1);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2234_; 
v_a_2211_ = lean_ctor_get(v_x_2200_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_x_2200_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2213_ = v_x_2200_;
v_isShared_2214_ = v_isSharedCheck_2234_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v_x_2200_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2234_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v_objects_2216_; lean_object* v_expireTime_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2233_; 
v___x_2215_ = lean_st_ref_take(v_val_2198_);
v_objects_2216_ = lean_ctor_get(v___x_2215_, 0);
v_expireTime_2217_ = lean_ctor_get(v___x_2215_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2219_ = v___x_2215_;
v_isShared_2220_ = v_isSharedCheck_2233_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_expireTime_2217_);
lean_inc(v_objects_2216_);
lean_dec(v___x_2215_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2233_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___f_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_2221_, 0, v_expireTime_2217_);
v___x_2222_ = l_Lean_Widget_instToJsonWidgetSource_toJson(v_a_2211_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v_objects_2216_);
lean_ctor_set(v___x_2219_, 0, v___x_2222_);
v___x_2224_ = v___x_2219_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_objects_2216_);
v___x_2224_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v_fst_2226_; lean_object* v_snd_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2225_ = l_Prod_map___redArg(v___f_2199_, v___f_2221_, v___x_2224_);
v_fst_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_fst_2226_);
v_snd_2227_ = lean_ctor_get(v___x_2225_, 1);
lean_inc(v_snd_2227_);
lean_dec_ref(v___x_2225_);
v___x_2228_ = lean_st_ref_put(v_val_2198_, v_snd_2227_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 0);
lean_ctor_set(v___x_2213_, 0, v_fst_2226_);
v___x_2230_ = v___x_2213_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_fst_2226_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2198_ = stack[0].m_obj;
lean_object* v___f_2199_ = stack[1].m_obj;
lean_object* v_x_2200_ = stack[2].m_obj;
lean_object* v___y_2201_ = stack[3].m_obj;
lean_object* v_res_2235_;
v_res_2235_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2198_, v___f_2199_, v_x_2200_, v___y_2201_);
stack->m_obj
 = v_res_2235_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed(lean_object* v_val_2236_, lean_object* v___f_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2(v_val_2236_, v___f_2237_, v_x_2238_, v___y_2239_);
lean_dec_ref(v___y_2239_);
lean_dec(v_val_2236_);
return v_res_2241_;
}
}
lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(lean_object* v___f_2249_, lean_object* v_method_2250_, lean_object* v_handler_2251_, uint64_t v_seshId_2252_, lean_object* v_j_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_rpcSessions_2256_; lean_object* v___x_2257_; 
v_rpcSessions_2256_ = lean_ctor_get(v___y_2254_, 0);
v___x_2257_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_2256_, v_seshId_2252_);
if (lean_obj_tag(v___x_2257_) == 1)
{
lean_object* v_val_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc_n(v_val_2258_, 2);
lean_dec_ref_known(v___x_2257_, 1);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2259_, 0, v_val_2258_);
lean_closure_set(v___f_2259_, 1, v___f_2249_);
v___x_2260_ = lean_st_ref_get(v_val_2258_);
lean_dec(v_val_2258_);
lean_dec(v___x_2260_);
lean_inc(v_j_2253_);
v___x_2261_ = l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson(v_j_2253_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v___f_2259_);
lean_dec_ref(v_handler_2251_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2282_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2282_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
uint8_t v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2266_ = 3;
v___x_2267_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_2268_ = 1;
v___x_2269_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2250_, v___x_2268_);
v___x_2270_ = lean_string_append(v___x_2267_, v___x_2269_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_2272_ = lean_string_append(v___x_2270_, v___x_2271_);
v___x_2273_ = l_Lean_Json_compress(v_j_2253_);
v___x_2274_ = lean_string_append(v___x_2272_, v___x_2273_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_2276_ = lean_string_append(v___x_2274_, v___x_2275_);
v___x_2277_ = lean_string_append(v___x_2276_, v_a_2262_);
lean_dec(v_a_2262_);
v___x_2278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*1, v___x_2266_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2278_);
v___x_2280_ = v___x_2264_;
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
else
{
lean_object* v_a_2283_; lean_object* v___x_2284_; 
lean_dec(v_j_2253_);
lean_dec(v_method_2250_);
v_a_2283_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2261_, 1);
lean_inc_ref(v___y_2254_);
v___x_2284_ = lean_apply_3(v_handler_2251_, v_a_2283_, v___y_2254_, lean_box(0));
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_2285_, v___f_2259_, v___y_2254_);
return v___x_2286_;
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___f_2259_);
v_a_2287_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2284_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2284_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec(v___x_2257_);
lean_dec(v_j_2253_);
lean_dec_ref(v_handler_2251_);
lean_dec(v_method_2250_);
lean_dec_ref(v___f_2249_);
v___x_2295_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2249_ = stack[0].m_obj;
lean_object* v_method_2250_ = stack[1].m_obj;
lean_object* v_handler_2251_ = stack[2].m_obj;
uint64_t v_seshId_2252_ = stack[3].m_num;
lean_object* v_j_2253_ = stack[4].m_obj;
lean_object* v___y_2254_ = stack[5].m_obj;
lean_object* v_res_2297_;
v_res_2297_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v___f_2249_, v_method_2250_, v_handler_2251_, v_seshId_2252_, v_j_2253_, v___y_2254_);
stack->m_obj
 = v_res_2297_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed(lean_object* v___f_2298_, lean_object* v_method_2299_, lean_object* v_handler_2300_, lean_object* v_seshId_2301_, lean_object* v_j_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint64_t v_seshId_boxed_2305_; lean_object* v_res_2306_; 
v_seshId_boxed_2305_ = lean_unbox_uint64(v_seshId_2301_);
lean_dec_ref(v_seshId_2301_);
v_res_2306_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3(v___f_2298_, v_method_2299_, v_handler_2300_, v_seshId_boxed_2305_, v_j_2302_, v___y_2303_);
lean_dec_ref(v___y_2303_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_method_2308_, lean_object* v_handler_2309_){
_start:
{
lean_object* v___f_2310_; lean_object* v___f_2311_; 
v___f_2310_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___boxed), 7, 3);
lean_closure_set(v___f_2311_, 0, v___f_2310_);
lean_closure_set(v___f_2311_, 1, v_method_2308_);
lean_closure_set(v___f_2311_, 2, v_handler_2309_);
return v___f_2311_;
}
}
lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(lean_object* v_method_2316_, lean_object* v_handler_2317_){
_start:
{
lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_errMsg_2324_; uint8_t v___x_2325_; 
v___x_2319_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_2320_ = 1;
lean_inc(v_method_2316_);
v___x_2321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2316_, v___x_2320_);
v___x_2322_ = lean_string_append(v___x_2319_, v___x_2321_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_2324_ = lean_string_append(v___x_2322_, v___x_2323_);
v___x_2325_ = l_Lean_initializing();
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v_handler_2317_);
lean_dec(v_method_2316_);
v___x_2326_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_2327_ = lean_string_append(v_errMsg_2324_, v___x_2326_);
v___x_2328_ = lean_mk_io_user_error(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_2331_ = lean_st_ref_get(v___x_2330_);
v___x_2332_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2331_, v_method_2316_);
lean_dec(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v_errMsg_2324_);
lean_inc(v_method_2316_);
v___x_2333_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1(v_method_2316_, v_handler_2317_);
v___x_2334_ = lean_st_ref_take(v___x_2330_);
v___x_2335_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2334_, v_method_2316_, v___x_2333_);
v___x_2336_ = lean_st_ref_put(v___x_2330_, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec_ref(v_handler_2317_);
lean_dec(v_method_2316_);
v___x_2338_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_2339_ = lean_string_append(v_errMsg_2324_, v___x_2338_);
v___x_2340_ = lean_mk_io_user_error(v___x_2339_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2316_ = stack[0].m_obj;
lean_object* v_handler_2317_ = stack[1].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2316_, v_handler_2317_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2343_, lean_object* v_handler_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v_method_2343_, v_handler_2344_);
return v_res_2346_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2355_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_));
v___x_2356_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0(v___x_2354_, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2357_;
v_res_2357_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2____boxed(lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2_();
return v_res_2359_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
uint8_t v___x_2363_; 
v___x_2363_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2361_, v_x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2361_ = stack[1].m_obj;
lean_object* v_x_2362_ = stack[2].m_obj;
uint8_t v_res_2364_;
v_res_2364_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_x_2361_, v_x_2362_);
stack->m_num = v_res_2364_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_){
_start:
{
uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_res_2368_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2365_, v_x_2366_, v_x_2367_);
lean_dec(v_x_2367_);
lean_dec_ref(v_x_2366_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_2370_){
_start:
{
lean_inc_ref(v_x_2370_);
return v_x_2370_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2371_);
lean_dec_ref(v_x_2371_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2373_, lean_object* v_x_2374_, lean_object* v___y_2375_){
_start:
{
lean_inc_ref(v_x_2374_);
return v_x_2374_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_x_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_MonadExcept_ofExcept___at___00Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b1_2376_, v_x_2377_, v___y_2378_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v_x_2377_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2381_, v_x_2382_, v_x_2383_);
return v___x_2384_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, size_t v_x_2387_, lean_object* v_x_2388_){
_start:
{
uint8_t v___x_2389_; 
v___x_2389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2386_, v_x_2387_, v_x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2386_ = stack[1].m_obj;
size_t v_x_2387_ = stack[2].m_num;
lean_object* v_x_2388_ = stack[3].m_obj;
uint8_t v_res_2390_;
v_res_2390_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_box(0), v_x_2386_, v_x_2387_, v_x_2388_);
stack->m_num = v_res_2390_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
size_t v_x_1997__boxed_2395_; uint8_t v_res_2396_; lean_object* v_r_2397_; 
v_x_1997__boxed_2395_ = lean_unbox_usize(v_x_2393_);
lean_dec(v_x_2393_);
v_res_2396_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2391_, v_x_2392_, v_x_1997__boxed_2395_, v_x_2394_);
lean_dec(v_x_2394_);
lean_dec_ref(v_x_2392_);
v_r_2397_ = lean_box(v_res_2396_);
return v_r_2397_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2398_, lean_object* v_x_2399_, size_t v_x_2400_, size_t v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_x_2399_, v_x_2400_, v_x_2401_, v_x_2402_, v_x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2399_ = stack[1].m_obj;
size_t v_x_2400_ = stack[2].m_num;
size_t v_x_2401_ = stack[3].m_num;
lean_object* v_x_2402_ = stack[4].m_obj;
lean_object* v_x_2403_ = stack[5].m_obj;
lean_object* v_res_2405_;
v_res_2405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_box(0), v_x_2399_, v_x_2400_, v_x_2401_, v_x_2402_, v_x_2403_);
stack->m_obj
 = v_res_2405_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
size_t v_x_2015__boxed_2412_; size_t v_x_2016__boxed_2413_; lean_object* v_res_2414_; 
v_x_2015__boxed_2412_ = lean_unbox_usize(v_x_2408_);
lean_dec(v_x_2408_);
v_x_2016__boxed_2413_ = lean_unbox_usize(v_x_2409_);
lean_dec(v_x_2409_);
v_res_2414_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_2406_, v_x_2407_, v_x_2015__boxed_2412_, v_x_2016__boxed_2413_, v_x_2410_, v_x_2411_);
return v_res_2414_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2415_, lean_object* v_keys_2416_, lean_object* v_vals_2417_, lean_object* v_heq_2418_, lean_object* v_i_2419_, lean_object* v_k_2420_){
_start:
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2416_, v_i_2419_, v_k_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2416_ = stack[1].m_obj;
lean_object* v_vals_2417_ = stack[2].m_obj;
lean_object* v_i_2419_ = stack[4].m_obj;
lean_object* v_k_2420_ = stack[5].m_obj;
uint8_t v_res_2422_;
v_res_2422_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_box(0), v_keys_2416_, v_vals_2417_, lean_box(0), v_i_2419_, v_k_2420_);
stack->m_num = v_res_2422_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2423_, lean_object* v_keys_2424_, lean_object* v_vals_2425_, lean_object* v_heq_2426_, lean_object* v_i_2427_, lean_object* v_k_2428_){
_start:
{
uint8_t v_res_2429_; lean_object* v_r_2430_; 
v_res_2429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2423_, v_keys_2424_, v_vals_2425_, v_heq_2426_, v_i_2427_, v_k_2428_);
lean_dec(v_k_2428_);
lean_dec_ref(v_vals_2425_);
lean_dec_ref(v_keys_2424_);
v_r_2430_ = lean_box(v_res_2429_);
return v_r_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_2431_, lean_object* v_n_2432_, lean_object* v_k_2433_, lean_object* v_v_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7___redArg(v_n_2432_, v_k_2433_, v_v_2434_);
return v___x_2435_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2436_, size_t v_depth_2437_, lean_object* v_keys_2438_, lean_object* v_vals_2439_, lean_object* v_heq_2440_, lean_object* v_i_2441_, lean_object* v_entries_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___redArg(v_depth_2437_, v_keys_2438_, v_vals_2439_, v_i_2441_, v_entries_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2437_ = stack[1].m_num;
lean_object* v_keys_2438_ = stack[2].m_obj;
lean_object* v_vals_2439_ = stack[3].m_obj;
lean_object* v_i_2441_ = stack[5].m_obj;
lean_object* v_entries_2442_ = stack[6].m_obj;
lean_object* v_res_2444_;
v_res_2444_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(lean_box(0), v_depth_2437_, v_keys_2438_, v_vals_2439_, lean_box(0), v_i_2441_, v_entries_2442_);
stack->m_obj
 = v_res_2444_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2445_, lean_object* v_depth_2446_, lean_object* v_keys_2447_, lean_object* v_vals_2448_, lean_object* v_heq_2449_, lean_object* v_i_2450_, lean_object* v_entries_2451_){
_start:
{
size_t v_depth_boxed_2452_; lean_object* v_res_2453_; 
v_depth_boxed_2452_ = lean_unbox_usize(v_depth_2446_);
lean_dec(v_depth_2446_);
v_res_2453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__8(v_00_u03b2_2445_, v_depth_boxed_2452_, v_keys_2447_, v_vals_2448_, v_heq_2449_, v_i_2450_, v_entries_2451_);
lean_dec_ref(v_vals_2448_);
lean_dec_ref(v_keys_2447_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_2454_, lean_object* v_x_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__7_spec__8___redArg(v_x_2455_, v_x_2456_, v_x_2457_, v_x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(lean_object* v_x_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_obj_tag_nat(v_x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl___boxed(lean_object* v_x_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorIdx___impl(v_x_2462_);
lean_dec_ref(v_x_2462_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(lean_object* v_t_2464_, lean_object* v_k_2465_){
_start:
{
if (lean_obj_tag(v_t_2464_) == 0)
{
lean_object* v_n_2466_; lean_object* v___x_2467_; 
v_n_2466_ = lean_ctor_get(v_t_2464_, 0);
lean_inc(v_n_2466_);
lean_dec_ref_known(v_t_2464_, 1);
v___x_2467_ = lean_apply_1(v_k_2465_, v_n_2466_);
return v___x_2467_;
}
else
{
lean_object* v_wi_2468_; lean_object* v___x_2469_; 
v_wi_2468_ = lean_ctor_get(v_t_2464_, 0);
lean_inc_ref(v_wi_2468_);
lean_dec_ref_known(v_t_2464_, 1);
v___x_2469_ = lean_apply_1(v_k_2465_, v_wi_2468_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(lean_object* v_motive_2470_, lean_object* v_ctorIdx_2471_, lean_object* v_t_2472_, lean_object* v_h_2473_, lean_object* v_k_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2472_, v_k_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___boxed(lean_object* v_motive_2476_, lean_object* v_ctorIdx_2477_, lean_object* v_t_2478_, lean_object* v_h_2479_, lean_object* v_k_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim(v_motive_2476_, v_ctorIdx_2477_, v_t_2478_, v_h_2479_, v_k_2480_);
lean_dec(v_ctorIdx_2477_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim___redArg(lean_object* v_t_2482_, lean_object* v_global_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2482_, v_global_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_global_elim(lean_object* v_motive_2485_, lean_object* v_t_2486_, lean_object* v_h_2487_, lean_object* v_global_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2486_, v_global_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim___redArg(lean_object* v_t_2490_, lean_object* v_local_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2490_, v_local_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_PanelWidgetsExtEntry_local_elim(lean_object* v_motive_2493_, lean_object* v_t_2494_, lean_object* v_h_2495_, lean_object* v_local_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Widget_PanelWidgetsExtEntry_ctorElim___redArg(v_t_2494_, v_local_2496_);
return v___x_2497_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2498_, uint64_t v_k_2499_, lean_object* v_fallback_2500_){
_start:
{
if (lean_obj_tag(v_t_2498_) == 0)
{
lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v_l_2503_; lean_object* v_r_2504_; uint64_t v___x_2505_; uint8_t v___x_2506_; 
v_k_2501_ = lean_ctor_get(v_t_2498_, 1);
v_v_2502_ = lean_ctor_get(v_t_2498_, 2);
v_l_2503_ = lean_ctor_get(v_t_2498_, 3);
v_r_2504_ = lean_ctor_get(v_t_2498_, 4);
v___x_2505_ = lean_unbox_uint64(v_k_2501_);
v___x_2506_ = lean_uint64_dec_lt(v_k_2499_, v___x_2505_);
if (v___x_2506_ == 0)
{
uint64_t v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = lean_unbox_uint64(v_k_2501_);
v___x_2508_ = lean_uint64_dec_eq(v_k_2499_, v___x_2507_);
if (v___x_2508_ == 0)
{
v_t_2498_ = v_r_2504_;
goto _start;
}
else
{
lean_inc(v_v_2502_);
return v_v_2502_;
}
}
else
{
v_t_2498_ = v_l_2503_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2500_);
return v_fallback_2500_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2498_ = stack[0].m_obj;
uint64_t v_k_2499_ = stack[1].m_num;
lean_object* v_fallback_2500_ = stack[2].m_obj;
lean_object* v_res_2511_;
v_res_2511_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2498_, v_k_2499_, v_fallback_2500_);
stack->m_obj
 = v_res_2511_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2512_, lean_object* v_k_2513_, lean_object* v_fallback_2514_){
_start:
{
uint64_t v_k_boxed_2515_; lean_object* v_res_2516_; 
v_k_boxed_2515_ = lean_unbox_uint64(v_k_2513_);
lean_dec_ref(v_k_2513_);
v_res_2516_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2512_, v_k_boxed_2515_, v_fallback_2514_);
lean_dec(v_fallback_2514_);
lean_dec(v_t_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__0_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_s_2517_, lean_object* v_x_2518_){
_start:
{
lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2533_; 
v_fst_2519_ = lean_ctor_get(v_x_2518_, 0);
v_snd_2520_ = lean_ctor_get(v_x_2518_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_x_2518_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2522_ = v_x_2518_;
v_isShared_2523_ = v_isSharedCheck_2533_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_snd_2520_);
lean_inc(v_fst_2519_);
lean_dec(v_x_2518_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2533_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; uint64_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_snd_2520_);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_unbox_uint64(v_fst_2519_);
v___x_2527_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_s_2517_, v___x_2526_, v___x_2525_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
lean_ctor_set(v___x_2522_, 1, v___x_2527_);
lean_ctor_set(v___x_2522_, 0, v___x_2524_);
v___x_2529_ = v___x_2522_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
uint64_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_unbox_uint64(v_fst_2519_);
lean_dec(v_fst_2519_);
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addBuiltinModule_spec__0___redArg(v___x_2530_, v___x_2529_, v_s_2517_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v_x_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_a_2535_);
lean_inc_ref_n(v___x_2536_, 2);
v___x_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_ctor_set(v___x_2537_, 2, v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_x_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__1_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v_x_2538_, v_a_2539_);
lean_dec_ref(v_x_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(lean_object* v___y_2541_){
_start:
{
lean_inc(v___y_2541_);
return v___y_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(v___y_2542_);
lean_dec(v___y_2542_);
return v_res_2543_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_));
v___x_2561_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2562_;
v_res_2562_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2____boxed(lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2_();
return v_res_2564_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2565_, lean_object* v_t_2566_, uint64_t v_k_2567_, lean_object* v_fallback_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___redArg(v_t_2566_, v_k_2567_, v_fallback_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2566_ = stack[1].m_obj;
uint64_t v_k_2567_ = stack[2].m_num;
lean_object* v_fallback_2568_ = stack[3].m_obj;
lean_object* v_res_2570_;
v_res_2570_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(lean_box(0), v_t_2566_, v_k_2567_, v_fallback_2568_);
stack->m_obj
 = v_res_2570_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2571_, lean_object* v_t_2572_, lean_object* v_k_2573_, lean_object* v_fallback_2574_){
_start:
{
uint64_t v_k_boxed_2575_; lean_object* v_res_2576_; 
v_k_boxed_2575_ = lean_unbox_uint64(v_k_2573_);
lean_dec_ref(v_k_2573_);
v_res_2576_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1015473889____hygCtx___hyg_2__spec__0(v_00_u03b4_2571_, v_t_2572_, v_k_boxed_2575_, v_fallback_2574_);
lean_dec(v_fallback_2574_);
lean_dec(v_t_2572_);
return v_res_2576_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(lean_object* v_as_x27_2577_, lean_object* v_b_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
if (lean_obj_tag(v_as_x27_2577_) == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_b_2578_);
return v___x_2584_;
}
else
{
lean_object* v_head_2585_; 
v_head_2585_ = lean_ctor_get(v_as_x27_2577_, 0);
if (lean_obj_tag(v_head_2585_) == 0)
{
lean_object* v_tail_2586_; lean_object* v_n_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_tail_2586_ = lean_ctor_get(v_as_x27_2577_, 1);
v_n_2587_ = lean_ctor_get(v_head_2585_, 0);
v___x_2588_ = lean_box(0);
lean_inc(v_n_2587_);
v___x_2589_ = l_Lean_mkConst(v_n_2587_, v___x_2588_);
v___x_2590_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v___x_2589_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = lean_array_push(v_b_2578_, v_a_2591_);
v_as_x27_2577_ = v_tail_2586_;
v_b_2578_ = v___x_2592_;
goto _start;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_b_2578_);
v_a_2594_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2590_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2590_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_tail_2602_; lean_object* v_wi_2603_; lean_object* v___x_2604_; 
v_tail_2602_ = lean_ctor_get(v_as_x27_2577_, 1);
v_wi_2603_ = lean_ctor_get(v_head_2585_, 0);
lean_inc_ref(v_wi_2603_);
v___x_2604_ = lean_array_push(v_b_2578_, v_wi_2603_);
v_as_x27_2577_ = v_tail_2602_;
v_b_2578_ = v___x_2604_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2577_ = stack[0].m_obj;
lean_object* v_b_2578_ = stack[1].m_obj;
lean_object* v___y_2579_ = stack[2].m_obj;
lean_object* v___y_2580_ = stack[3].m_obj;
lean_object* v___y_2581_ = stack[4].m_obj;
lean_object* v___y_2582_ = stack[5].m_obj;
lean_object* v_res_2606_;
v_res_2606_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2577_, v_b_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
stack->m_obj
 = v_res_2606_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg___boxed(lean_object* v_as_x27_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2607_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v_as_x27_2607_);
return v_res_2614_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(lean_object* v_init_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
if (lean_obj_tag(v_x_2616_) == 0)
{
lean_object* v_v_2622_; lean_object* v_l_2623_; lean_object* v_r_2624_; lean_object* v___x_2625_; 
v_v_2622_ = lean_ctor_get(v_x_2616_, 2);
v_l_2623_ = lean_ctor_get(v_x_2616_, 3);
v_r_2624_ = lean_ctor_get(v_x_2616_, 4);
v___x_2625_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2615_, v_l_2623_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v_a_2627_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_a_2627_);
lean_dec(v_a_2626_);
v___x_2628_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_v_2622_, v_a_2627_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v_init_2615_ = v_a_2629_;
v_x_2616_ = v_r_2624_;
goto _start;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2628_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2628_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
return v___x_2625_;
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_init_2615_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2615_ = stack[0].m_obj;
lean_object* v_x_2616_ = stack[1].m_obj;
lean_object* v___y_2617_ = stack[2].m_obj;
lean_object* v___y_2618_ = stack[3].m_obj;
lean_object* v___y_2619_ = stack[4].m_obj;
lean_object* v___y_2620_ = stack[5].m_obj;
lean_object* v_res_2641_;
v_res_2641_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2615_, v_x_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
stack->m_obj
 = v_res_2641_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1___boxed(lean_object* v_init_2642_, lean_object* v_x_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_init_2642_, v_x_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v_x_2643_);
return v_res_2649_;
}
}
lean_object* l_Lean_Widget_evalPanelWidgets(lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_ret_2657_; lean_object* v___x_2658_; lean_object* v_env_2659_; lean_object* v___x_2660_; lean_object* v_ext_2661_; lean_object* v_toEnvExtension_2662_; lean_object* v_asyncMode_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_ret_2657_ = ((lean_object*)(l_Lean_Widget_evalPanelWidgets___closed__0));
v___x_2658_ = lean_st_ref_get(v_a_2655_);
v_env_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc_ref(v_env_2659_);
lean_dec(v___x_2658_);
v___x_2660_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v_ext_2661_ = lean_ctor_get(v___x_2660_, 1);
v_toEnvExtension_2662_ = lean_ctor_get(v_ext_2661_, 0);
v_asyncMode_2663_ = lean_ctor_get(v_toEnvExtension_2662_, 2);
v___x_2664_ = lean_box(1);
v___x_2665_ = 0;
v___x_2666_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2664_, v___x_2660_, v_env_2659_, v_asyncMode_2663_, v___x_2665_);
v___x_2667_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Widget_evalPanelWidgets_spec__1(v_ret_2657_, v___x_2666_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v___x_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2676_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_a_2672_; lean_object* v___x_2674_; 
v_a_2672_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_a_2672_);
lean_dec(v_a_2668_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v_a_2672_);
v___x_2674_ = v___x_2670_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2667_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2667_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_evalPanelWidgets_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2652_ = stack[0].m_obj;
lean_object* v_a_2653_ = stack[1].m_obj;
lean_object* v_a_2654_ = stack[2].m_obj;
lean_object* v_a_2655_ = stack[3].m_obj;
lean_object* v_res_2685_;
v_res_2685_ = l_Lean_Widget_evalPanelWidgets(v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
stack->m_obj
 = v_res_2685_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_evalPanelWidgets___boxed(lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Widget_evalPanelWidgets(v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
return v_res_2691_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(lean_object* v_as_2692_, lean_object* v_as_x27_2693_, lean_object* v_b_2694_, lean_object* v_a_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___redArg(v_as_x27_2693_, v_b_2694_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2692_ = stack[0].m_obj;
lean_object* v_as_x27_2693_ = stack[1].m_obj;
lean_object* v_b_2694_ = stack[2].m_obj;
lean_object* v___y_2696_ = stack[4].m_obj;
lean_object* v___y_2697_ = stack[5].m_obj;
lean_object* v___y_2698_ = stack[6].m_obj;
lean_object* v___y_2699_ = stack[7].m_obj;
lean_object* v_res_2702_;
v_res_2702_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2692_, v_as_x27_2693_, v_b_2694_, lean_box(0), v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
stack->m_obj
 = v_res_2702_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0___boxed(lean_object* v_as_2703_, lean_object* v_as_x27_2704_, lean_object* v_b_2705_, lean_object* v_a_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_List_forIn_x27_loop___at___00Lean_Widget_evalPanelWidgets_spec__0(v_as_2703_, v_as_x27_2704_, v_b_2705_, v_a_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_as_x27_2704_);
lean_dec(v_as_2703_);
return v_res_2712_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg(lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, uint64_t v_h_2716_, lean_object* v_n_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; 
v___x_2718_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2719_ = lean_box_uint64(v_h_2716_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_n_2717_);
v___x_2721_ = 0;
v___x_2722_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2713_, v_inst_2715_, v_inst_2714_, v___x_2718_, v___x_2720_, v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetGlobal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2713_ = stack[0].m_obj;
lean_object* v_inst_2714_ = stack[1].m_obj;
lean_object* v_inst_2715_ = stack[2].m_obj;
uint64_t v_h_2716_ = stack[3].m_num;
lean_object* v_n_2717_ = stack[4].m_obj;
lean_object* v_res_2723_;
v_res_2723_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2713_, v_inst_2714_, v_inst_2715_, v_h_2716_, v_n_2717_);
stack->m_obj
 = v_res_2723_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___redArg___boxed(lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_h_2727_, lean_object* v_n_2728_){
_start:
{
uint64_t v_h_boxed_2729_; lean_object* v_res_2730_; 
v_h_boxed_2729_ = lean_unbox_uint64(v_h_2727_);
lean_dec_ref(v_h_2727_);
v_res_2730_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2724_, v_inst_2725_, v_inst_2726_, v_h_boxed_2729_, v_n_2728_);
return v_res_2730_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetGlobal(lean_object* v_m_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, uint64_t v_h_2735_, lean_object* v_n_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_Widget_addPanelWidgetGlobal___redArg(v_inst_2732_, v_inst_2733_, v_inst_2734_, v_h_2735_, v_n_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetGlobal_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2732_ = stack[1].m_obj;
lean_object* v_inst_2733_ = stack[2].m_obj;
lean_object* v_inst_2734_ = stack[3].m_obj;
uint64_t v_h_2735_ = stack[4].m_num;
lean_object* v_n_2736_ = stack[5].m_obj;
lean_object* v_res_2738_;
v_res_2738_ = l_Lean_Widget_addPanelWidgetGlobal(lean_box(0), v_inst_2732_, v_inst_2733_, v_inst_2734_, v_h_2735_, v_n_2736_);
stack->m_obj
 = v_res_2738_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetGlobal___boxed(lean_object* v_m_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_h_2743_, lean_object* v_n_2744_){
_start:
{
uint64_t v_h_boxed_2745_; lean_object* v_res_2746_; 
v_h_boxed_2745_ = lean_unbox_uint64(v_h_2743_);
lean_dec_ref(v_h_2743_);
v_res_2746_ = l_Lean_Widget_addPanelWidgetGlobal(v_m_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_h_boxed_2745_, v_n_2744_);
return v_res_2746_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg(lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, uint64_t v_h_2750_, lean_object* v_n_2751_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2752_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2753_ = lean_box_uint64(v_h_2750_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v_n_2751_);
v___x_2755_ = 2;
v___x_2756_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2747_, v_inst_2749_, v_inst_2748_, v___x_2752_, v___x_2754_, v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetScoped___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2747_ = stack[0].m_obj;
lean_object* v_inst_2748_ = stack[1].m_obj;
lean_object* v_inst_2749_ = stack[2].m_obj;
uint64_t v_h_2750_ = stack[3].m_num;
lean_object* v_n_2751_ = stack[4].m_obj;
lean_object* v_res_2757_;
v_res_2757_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2747_, v_inst_2748_, v_inst_2749_, v_h_2750_, v_n_2751_);
stack->m_obj
 = v_res_2757_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___redArg___boxed(lean_object* v_inst_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_h_2761_, lean_object* v_n_2762_){
_start:
{
uint64_t v_h_boxed_2763_; lean_object* v_res_2764_; 
v_h_boxed_2763_ = lean_unbox_uint64(v_h_2761_);
lean_dec_ref(v_h_2761_);
v_res_2764_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2758_, v_inst_2759_, v_inst_2760_, v_h_boxed_2763_, v_n_2762_);
return v_res_2764_;
}
}
lean_object* l_Lean_Widget_addPanelWidgetScoped(lean_object* v_m_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_inst_2768_, uint64_t v_h_2769_, lean_object* v_n_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Widget_addPanelWidgetScoped___redArg(v_inst_2766_, v_inst_2767_, v_inst_2768_, v_h_2769_, v_n_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetScoped_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2766_ = stack[1].m_obj;
lean_object* v_inst_2767_ = stack[2].m_obj;
lean_object* v_inst_2768_ = stack[3].m_obj;
uint64_t v_h_2769_ = stack[4].m_num;
lean_object* v_n_2770_ = stack[5].m_obj;
lean_object* v_res_2772_;
v_res_2772_ = l_Lean_Widget_addPanelWidgetScoped(lean_box(0), v_inst_2766_, v_inst_2767_, v_inst_2768_, v_h_2769_, v_n_2770_);
stack->m_obj
 = v_res_2772_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetScoped___boxed(lean_object* v_m_2773_, lean_object* v_inst_2774_, lean_object* v_inst_2775_, lean_object* v_inst_2776_, lean_object* v_h_2777_, lean_object* v_n_2778_){
_start:
{
uint64_t v_h_boxed_2779_; lean_object* v_res_2780_; 
v_h_boxed_2779_ = lean_unbox_uint64(v_h_2777_);
lean_dec_ref(v_h_2777_);
v_res_2780_ = l_Lean_Widget_addPanelWidgetScoped(v_m_2773_, v_inst_2774_, v_inst_2775_, v_inst_2776_, v_h_boxed_2779_, v_n_2778_);
return v_res_2780_;
}
}
uint8_t l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(uint64_t v_x_2781_, uint64_t v_y_2782_){
_start:
{
uint8_t v___x_2783_; 
v___x_2783_ = lean_uint64_dec_lt(v_x_2781_, v_y_2782_);
if (v___x_2783_ == 0)
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_uint64_dec_eq(v_x_2781_, v_y_2782_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = 2;
return v___x_2785_;
}
else
{
uint8_t v___x_2786_; 
v___x_2786_ = 1;
return v___x_2786_;
}
}
else
{
uint8_t v___x_2787_; 
v___x_2787_ = 0;
return v___x_2787_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_2781_ = stack[0].m_num;
uint64_t v_y_2782_ = stack[1].m_num;
uint8_t v_res_2788_;
v_res_2788_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_2781_, v_y_2782_);
stack->m_num = v_res_2788_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0___boxed(lean_object* v_x_2789_, lean_object* v_y_2790_){
_start:
{
uint64_t v_x_boxed_2791_; uint64_t v_y_boxed_2792_; uint8_t v_res_2793_; lean_object* v_r_2794_; 
v_x_boxed_2791_ = lean_unbox_uint64(v_x_2789_);
lean_dec_ref(v_x_2789_);
v_y_boxed_2792_ = lean_unbox_uint64(v_y_2790_);
lean_dec_ref(v_y_2790_);
v_res_2793_ = l_Lean_Widget_addPanelWidgetLocal___redArg___lam__0(v_x_boxed_2791_, v_y_boxed_2792_);
v_r_2794_ = lean_box(v_res_2793_);
return v_r_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1(lean_object* v_wi_2795_, lean_object* v___f_2796_, lean_object* v_s_2797_){
_start:
{
uint64_t v_javascriptHash_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_javascriptHash_2798_ = lean_ctor_get_uint64(v_wi_2795_, sizeof(void*)*2);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v_wi_2795_);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_box_uint64(v_javascriptHash_2798_);
lean_inc(v_s_2797_);
lean_inc_ref(v___f_2796_);
v___x_2802_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v___f_2796_, v_s_2797_, v___x_2801_, v___x_2800_);
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2799_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_box_uint64(v_javascriptHash_2798_);
v___x_2805_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_2796_, v___x_2804_, v___x_2803_, v_s_2797_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2(lean_object* v___f_2806_, lean_object* v_env_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
v___x_2809_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2808_, v_env_2807_, v___f_2806_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___redArg(lean_object* v_inst_2811_, lean_object* v_wi_2812_){
_start:
{
lean_object* v_modifyEnv_2813_; lean_object* v___f_2814_; lean_object* v___f_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; 
v_modifyEnv_2813_ = lean_ctor_get(v_inst_2811_, 1);
lean_inc(v_modifyEnv_2813_);
lean_dec_ref(v_inst_2811_);
v___f_2814_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___f_2815_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2815_, 0, v_wi_2812_);
lean_closure_set(v___f_2815_, 1, v___f_2814_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2816_, 0, v___f_2815_);
v___x_2817_ = lean_apply_1(v_modifyEnv_2813_, v___f_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal(lean_object* v_m_2818_, lean_object* v_inst_2819_, lean_object* v_inst_2820_, lean_object* v_wi_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Widget_addPanelWidgetLocal___redArg(v_inst_2820_, v_wi_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_addPanelWidgetLocal___boxed(lean_object* v_m_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_wi_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_Widget_addPanelWidgetLocal(v_m_2823_, v_inst_2824_, v_inst_2825_, v_wi_2826_);
lean_dec_ref(v_inst_2824_);
return v_res_2827_;
}
}
lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1(lean_object* v___f_2828_, uint64_t v_h_2829_, lean_object* v_st_2830_){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_box_uint64(v_h_2829_);
v___x_2832_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___f_2828_, v___x_2831_, v_st_2830_);
return v___x_2832_;
}
}
LEAN_EXPORT void l_Lean_Widget_erasePanelWidget___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2828_ = stack[0].m_obj;
uint64_t v_h_2829_ = stack[1].m_num;
lean_object* v_st_2830_ = stack[2].m_obj;
lean_object* v_res_2833_;
v_res_2833_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2828_, v_h_2829_, v_st_2830_);
stack->m_obj
 = v_res_2833_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed(lean_object* v___f_2834_, lean_object* v_h_2835_, lean_object* v_st_2836_){
_start:
{
uint64_t v_h_boxed_2837_; lean_object* v_res_2838_; 
v_h_boxed_2837_ = lean_unbox_uint64(v_h_2835_);
lean_dec_ref(v_h_2835_);
v_res_2838_ = l_Lean_Widget_erasePanelWidget___redArg___lam__1(v___f_2834_, v_h_boxed_2837_, v_st_2836_);
return v_res_2838_;
}
}
lean_object* l_Lean_Widget_erasePanelWidget___redArg(lean_object* v_inst_2839_, uint64_t v_h_2840_){
_start:
{
lean_object* v_modifyEnv_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___f_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; 
v_modifyEnv_2841_ = lean_ctor_get(v_inst_2839_, 1);
lean_inc(v_modifyEnv_2841_);
lean_dec_ref(v_inst_2839_);
v___f_2842_ = ((lean_object*)(l_Lean_Widget_addPanelWidgetLocal___redArg___closed__0));
v___x_2843_ = lean_box_uint64(v_h_2840_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_Widget_erasePanelWidget___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2844_, 0, v___f_2842_);
lean_closure_set(v___f_2844_, 1, v___x_2843_);
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_Widget_addPanelWidgetLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2845_, 0, v___f_2844_);
v___x_2846_ = lean_apply_1(v_modifyEnv_2841_, v___f_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT void l_Lean_Widget_erasePanelWidget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2839_ = stack[0].m_obj;
uint64_t v_h_2840_ = stack[1].m_num;
lean_object* v_res_2847_;
v_res_2847_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2839_, v_h_2840_);
stack->m_obj
 = v_res_2847_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___redArg___boxed(lean_object* v_inst_2848_, lean_object* v_h_2849_){
_start:
{
uint64_t v_h_boxed_2850_; lean_object* v_res_2851_; 
v_h_boxed_2850_ = lean_unbox_uint64(v_h_2849_);
lean_dec_ref(v_h_2849_);
v_res_2851_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2848_, v_h_boxed_2850_);
return v_res_2851_;
}
}
lean_object* l_Lean_Widget_erasePanelWidget(lean_object* v_m_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, uint64_t v_h_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_Widget_erasePanelWidget___redArg(v_inst_2854_, v_h_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT void l_Lean_Widget_erasePanelWidget_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2853_ = stack[1].m_obj;
lean_object* v_inst_2854_ = stack[2].m_obj;
uint64_t v_h_2855_ = stack[3].m_num;
lean_object* v_res_2857_;
v_res_2857_ = l_Lean_Widget_erasePanelWidget(lean_box(0), v_inst_2853_, v_inst_2854_, v_h_2855_);
stack->m_obj
 = v_res_2857_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_erasePanelWidget___boxed(lean_object* v_m_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_h_2861_){
_start:
{
uint64_t v_h_boxed_2862_; lean_object* v_res_2863_; 
v_h_boxed_2862_ = lean_unbox_uint64(v_h_2861_);
lean_dec_ref(v_h_2861_);
v_res_2863_ = l_Lean_Widget_erasePanelWidget(v_m_2858_, v_inst_2859_, v_inst_2860_, v_h_boxed_2862_);
lean_dec_ref(v_inst_2859_);
return v_res_2863_;
}
}
lean_object* l_Lean_Widget_WidgetInstance_ofHash(uint64_t v_hash_2864_, lean_object* v_props_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v_env_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v_val_2874_; lean_object* v___x_2877_; 
v___x_2869_ = lean_st_ref_get(v_a_2867_);
v_env_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc_ref(v_env_2870_);
lean_dec(v___x_2869_);
v___x_2871_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_builtinModulesRef;
v___x_2872_ = lean_st_ref_get(v___x_2871_);
v___x_2877_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_2872_, v_hash_2864_);
lean_dec(v___x_2872_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v___x_2878_; lean_object* v_toEnvExtension_2879_; lean_object* v_asyncMode_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2878_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_moduleRegistry;
v_toEnvExtension_2879_ = lean_ctor_get(v___x_2878_, 0);
v_asyncMode_2880_ = lean_ctor_get(v_toEnvExtension_2879_, 2);
v___x_2881_ = lean_box(1);
v___x_2882_ = lean_box(0);
v___x_2883_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2881_, v___x_2878_, v_env_2870_, v_asyncMode_2880_, v___x_2882_);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v___x_2883_, v_hash_2864_);
lean_dec(v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_dec_ref(v_props_2865_);
v___x_2885_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__0));
v___x_2886_ = lean_uint64_to_nat(v_hash_2864_);
v___x_2887_ = l_Nat_reprFast(v___x_2886_);
v___x_2888_ = lean_string_append(v___x_2885_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = ((lean_object*)(l_Lean_Widget_getWidgetSource___closed__1));
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
v___x_2892_ = l_Lean_MessageData_ofFormat(v___x_2891_);
v___x_2893_ = l_Lean_throwError___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__0___redArg(v___x_2892_, v_a_2866_, v_a_2867_);
return v___x_2893_;
}
else
{
lean_object* v_val_2894_; lean_object* v_fst_2895_; 
v_val_2894_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2894_);
lean_dec_ref_known(v___x_2884_, 1);
v_fst_2895_ = lean_ctor_get(v_val_2894_, 0);
lean_inc(v_fst_2895_);
lean_dec(v_val_2894_);
v_val_2874_ = v_fst_2895_;
goto v___jp_2873_;
}
}
else
{
lean_object* v_val_2896_; lean_object* v_fst_2897_; 
lean_dec_ref(v_env_2870_);
v_val_2896_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_val_2896_);
lean_dec_ref_known(v___x_2877_, 1);
v_fst_2897_ = lean_ctor_get(v_val_2896_, 0);
lean_inc(v_fst_2897_);
lean_dec(v_val_2896_);
v_val_2874_ = v_fst_2897_;
goto v___jp_2873_;
}
v___jp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2875_, 0, v_val_2874_);
lean_ctor_set(v___x_2875_, 1, v_props_2865_);
lean_ctor_set_uint64(v___x_2875_, sizeof(void*)*2, v_hash_2864_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_WidgetInstance_ofHash_0interp(lean_interpreter_value* stack)
{
uint64_t v_hash_2864_ = stack[0].m_num;
lean_object* v_props_2865_ = stack[1].m_obj;
lean_object* v_a_2866_ = stack[2].m_obj;
lean_object* v_a_2867_ = stack[3].m_obj;
lean_object* v_res_2898_;
v_res_2898_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2864_, v_props_2865_, v_a_2866_, v_a_2867_);
stack->m_obj
 = v_res_2898_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_WidgetInstance_ofHash___boxed(lean_object* v_hash_2899_, lean_object* v_props_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
uint64_t v_hash_boxed_2904_; lean_object* v_res_2905_; 
v_hash_boxed_2904_ = lean_unbox_uint64(v_hash_2899_);
lean_dec_ref(v_hash_2899_);
v_res_2905_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_boxed_2904_, v_props_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2905_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(lean_object* v_t_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; lean_object* v_infoState_2910_; uint8_t v_enabled_2911_; 
v___x_2909_ = lean_st_ref_get(v___y_2907_);
v_infoState_2910_ = lean_ctor_get(v___x_2909_, 8);
lean_inc_ref(v_infoState_2910_);
lean_dec(v___x_2909_);
v_enabled_2911_ = lean_ctor_get_uint8(v_infoState_2910_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2910_);
if (v_enabled_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec_ref(v_t_2906_);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; lean_object* v_infoState_2915_; lean_object* v_env_2916_; lean_object* v_nextMacroScope_2917_; lean_object* v_ngen_2918_; lean_object* v_auxDeclNGen_2919_; lean_object* v_traceState_2920_; lean_object* v_cache_2921_; lean_object* v_recordedDeps_2922_; lean_object* v_messages_2923_; lean_object* v_snapshotTasks_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2946_; 
v___x_2914_ = lean_st_ref_take(v___y_2907_);
v_infoState_2915_ = lean_ctor_get(v___x_2914_, 8);
v_env_2916_ = lean_ctor_get(v___x_2914_, 0);
v_nextMacroScope_2917_ = lean_ctor_get(v___x_2914_, 1);
v_ngen_2918_ = lean_ctor_get(v___x_2914_, 2);
v_auxDeclNGen_2919_ = lean_ctor_get(v___x_2914_, 3);
v_traceState_2920_ = lean_ctor_get(v___x_2914_, 4);
v_cache_2921_ = lean_ctor_get(v___x_2914_, 5);
v_recordedDeps_2922_ = lean_ctor_get(v___x_2914_, 6);
v_messages_2923_ = lean_ctor_get(v___x_2914_, 7);
v_snapshotTasks_2924_ = lean_ctor_get(v___x_2914_, 9);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2926_ = v___x_2914_;
v_isShared_2927_ = v_isSharedCheck_2946_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_snapshotTasks_2924_);
lean_inc(v_infoState_2915_);
lean_inc(v_messages_2923_);
lean_inc(v_recordedDeps_2922_);
lean_inc(v_cache_2921_);
lean_inc(v_traceState_2920_);
lean_inc(v_auxDeclNGen_2919_);
lean_inc(v_ngen_2918_);
lean_inc(v_nextMacroScope_2917_);
lean_inc(v_env_2916_);
lean_dec(v___x_2914_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2946_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
uint8_t v_enabled_2928_; lean_object* v_assignment_2929_; lean_object* v_lazyAssignment_2930_; lean_object* v_trees_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2945_; 
v_enabled_2928_ = lean_ctor_get_uint8(v_infoState_2915_, sizeof(void*)*3);
v_assignment_2929_ = lean_ctor_get(v_infoState_2915_, 0);
v_lazyAssignment_2930_ = lean_ctor_get(v_infoState_2915_, 1);
v_trees_2931_ = lean_ctor_get(v_infoState_2915_, 2);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_infoState_2915_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2933_ = v_infoState_2915_;
v_isShared_2934_ = v_isSharedCheck_2945_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_trees_2931_);
lean_inc(v_lazyAssignment_2930_);
lean_inc(v_assignment_2929_);
lean_dec(v_infoState_2915_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2945_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2935_ = lean_box(0);
v___x_2936_ = l_Lean_PersistentArray_push___redArg(v_trees_2931_, v_t_2906_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 2, v___x_2936_);
v___x_2938_ = v___x_2933_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_assignment_2929_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_lazyAssignment_2930_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v___x_2936_);
lean_ctor_set_uint8(v_reuseFailAlloc_2944_, sizeof(void*)*3, v_enabled_2928_);
v___x_2938_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2940_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 8, v___x_2938_);
v___x_2940_ = v___x_2926_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_env_2916_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_nextMacroScope_2917_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_ngen_2918_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_auxDeclNGen_2919_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_traceState_2920_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v_cache_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 6, v_recordedDeps_2922_);
lean_ctor_set(v_reuseFailAlloc_2943_, 7, v_messages_2923_);
lean_ctor_set(v_reuseFailAlloc_2943_, 8, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2943_, 9, v_snapshotTasks_2924_);
v___x_2940_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_st_ref_put(v___y_2907_, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2935_);
return v___x_2942_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2906_ = stack[0].m_obj;
lean_object* v___y_2907_ = stack[1].m_obj;
lean_object* v_res_2947_;
v_res_2947_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2906_, v___y_2907_);
stack->m_obj
 = v_res_2947_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_2948_, v___y_2949_);
lean_dec(v___y_2949_);
return v_res_2951_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_unsigned_to_nat(32u);
v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2955_ = ((size_t)5ULL);
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_unsigned_to_nat(32u);
v___x_2958_ = lean_mk_empty_array_with_capacity(v___x_2957_);
v___x_2959_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__0);
v___x_2960_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___x_2958_);
lean_ctor_set(v___x_2960_, 2, v___x_2956_);
lean_ctor_set(v___x_2960_, 3, v___x_2956_);
lean_ctor_set_usize(v___x_2960_, 4, v___x_2955_);
return v___x_2960_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(lean_object* v_t_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; lean_object* v_infoState_2966_; uint8_t v_enabled_2967_; 
v___x_2965_ = lean_st_ref_get(v___y_2963_);
v_infoState_2966_ = lean_ctor_get(v___x_2965_, 8);
lean_inc_ref(v_infoState_2966_);
lean_dec(v___x_2965_);
v_enabled_2967_ = lean_ctor_get_uint8(v_infoState_2966_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2966_);
if (v_enabled_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec_ref(v_t_2961_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___closed__1);
v___x_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_t_2961_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v___x_2971_, v___y_2963_);
return v___x_2972_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2961_ = stack[0].m_obj;
lean_object* v___y_2962_ = stack[1].m_obj;
lean_object* v___y_2963_ = stack[2].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2961_, v___y_2962_, v___y_2963_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0___boxed(lean_object* v_t_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v_t_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
return v_res_2978_;
}
}
lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t v_hash_2979_, lean_object* v_props_2980_, lean_object* v_stx_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_Widget_WidgetInstance_ofHash(v_hash_2979_, v_props_2980_, v_a_2982_, v_a_2983_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2986_);
lean_ctor_set(v___x_2987_, 1, v_stx_2981_);
v___x_2988_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
v___x_2989_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0(v___x_2988_, v_a_2982_, v_a_2983_);
return v___x_2989_;
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_stx_2981_);
v_a_2990_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2985_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2985_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_savePanelWidgetInfo_0interp(lean_interpreter_value* stack)
{
uint64_t v_hash_2979_ = stack[0].m_num;
lean_object* v_props_2980_ = stack[1].m_obj;
lean_object* v_stx_2981_ = stack[2].m_obj;
lean_object* v_a_2982_ = stack[3].m_obj;
lean_object* v_a_2983_ = stack[4].m_obj;
lean_object* v_res_2998_;
v_res_2998_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_2979_, v_props_2980_, v_stx_2981_, v_a_2982_, v_a_2983_);
stack->m_obj
 = v_res_2998_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_savePanelWidgetInfo___boxed(lean_object* v_hash_2999_, lean_object* v_props_3000_, lean_object* v_stx_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
uint64_t v_hash_boxed_3005_; lean_object* v_res_3006_; 
v_hash_boxed_3005_ = lean_unbox_uint64(v_hash_2999_);
lean_dec_ref(v_hash_2999_);
v_res_3006_ = l_Lean_Widget_savePanelWidgetInfo(v_hash_boxed_3005_, v_props_3000_, v_stx_3001_, v_a_3002_, v_a_3003_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
return v_res_3006_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(lean_object* v_t_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___redArg(v_t_3007_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3007_ = stack[0].m_obj;
lean_object* v___y_3008_ = stack[1].m_obj;
lean_object* v___y_3009_ = stack[2].m_obj;
lean_object* v_res_3012_;
v_res_3012_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_3007_, v___y_3008_, v___y_3009_);
stack->m_obj
 = v_res_3012_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0___boxed(lean_object* v_t_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Widget_savePanelWidgetInfo_spec__0_spec__0(v_t_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonUserWidgetDefinition_toJson(lean_object* v_x_3024_){
_start:
{
lean_object* v_name_3025_; lean_object* v_javascript_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3046_; 
v_name_3025_ = lean_ctor_get(v_x_3024_, 0);
v_javascript_3026_ = lean_ctor_get(v_x_3024_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_x_3024_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3028_ = v_x_3024_;
v_isShared_3029_ = v_isSharedCheck_3046_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_javascript_3026_);
lean_inc(v_name_3025_);
lean_dec(v_x_3024_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3046_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3030_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_name_3025_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3031_);
lean_ctor_set(v___x_3028_, 0, v___x_3030_);
v___x_3033_ = v___x_3028_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_3037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_javascript_3026_);
v___x_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3034_);
v___x_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3034_);
v___x_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3035_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3043_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3041_, v___x_3042_);
v___x_3044_ = l_Lean_Json_mkObj(v___x_3043_);
lean_dec(v___x_3043_);
return v___x_3044_;
}
}
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = 1;
v___x_3055_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3056_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3055_, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__2___closed__3_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_));
v___x_3058_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__2);
v___x_3059_ = lean_string_append(v___x_3058_, v___x_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = 1;
v___x_3063_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__4));
v___x_3064_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3063_, v___x_3062_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__5);
v___x_3066_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_3067_ = lean_string_append(v___x_3066_, v___x_3065_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_3069_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__6);
v___x_3070_ = lean_string_append(v___x_3069_, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = 1;
v___x_3074_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__8));
v___x_3075_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3074_, v___x_3073_);
return v___x_3075_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__9);
v___x_3077_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__3);
v___x_3078_ = lean_string_append(v___x_3077_, v___x_3076_);
return v___x_3078_;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((lean_object*)(l_Lean_Widget_instFromJsonGetWidgetSourceParams_fromJson___closed__7));
v___x_3080_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__10);
v___x_3081_ = lean_string_append(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson(lean_object* v_json_3082_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
lean_inc(v_json_3082_);
v___x_3084_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3082_, v___x_3083_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_json_3082_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3094_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3094_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3089_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__7);
v___x_3090_ = lean_string_append(v___x_3089_, v_a_3085_);
lean_dec(v_a_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3090_);
v___x_3092_ = v___x_3087_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
else
{
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_json_3082_);
v_a_3095_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3084_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3084_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 0);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_a_3103_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3084_, 1);
v___x_3104_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__1));
v___x_3105_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonWidgetSource_fromJson_spec__0(v_json_3082_, v___x_3104_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3103_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3115_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3110_ = lean_obj_once(&l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11, &l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11_once, _init_l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__11);
v___x_3111_ = lean_string_append(v___x_3110_, v_a_3106_);
lean_dec(v_a_3106_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3111_);
v___x_3113_ = v___x_3108_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_a_3103_);
v_a_3116_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3105_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3105_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 0);
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3132_; 
v_a_3124_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3126_ = v___x_3105_;
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3105_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v_a_3103_);
lean_ctor_set(v___x_3128_, 1, v_a_3124_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3128_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(lean_object* v_uwd_3135_){
_start:
{
lean_object* v_javascript_3136_; uint64_t v___x_3137_; lean_object* v___x_3138_; 
v_javascript_3136_ = lean_ctor_get(v_uwd_3135_, 1);
v___x_3137_ = lean_string_hash(v_javascript_3136_);
lean_inc_ref(v_javascript_3136_);
v___x_3138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3138_, 0, v_javascript_3136_);
lean_ctor_set_uint64(v___x_3138_, sizeof(void*)*1, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0___boxed(lean_object* v_uwd_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Widget_instToModuleUserWidgetDefinition___lam__0(v_uwd_3139_);
lean_dec_ref(v_uwd_3139_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(lean_object* v_____do__lift_3143_, lean_object* v_id_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v___x_3147_, lean_object* v_____do__lift_3148_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3150_ = l_Lean_Environment_evalConstCheck___redArg(v_____do__lift_3143_, v_____do__lift_3148_, v___x_3149_, v_id_3144_);
v___x_3151_ = l_Lean_ofExcept___redArg(v_inst_3145_, v_inst_3146_, v___x_3147_, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed(lean_object* v_____do__lift_3152_, lean_object* v_id_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v___x_3156_, lean_object* v_____do__lift_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0(v_____do__lift_3152_, v_id_3153_, v_inst_3154_, v_inst_3155_, v___x_3156_, v_____do__lift_3157_);
lean_dec_ref(v_____do__lift_3157_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1(lean_object* v_inst_3159_, lean_object* v_id_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v___x_3163_, lean_object* v_toBind_3164_, lean_object* v_____do__lift_3165_){
_start:
{
lean_object* v_getOptions_3166_; lean_object* v___f_3167_; lean_object* v___x_3168_; 
v_getOptions_3166_ = lean_ctor_get(v_inst_3159_, 0);
lean_inc(v_getOptions_3166_);
lean_dec_ref(v_inst_3159_);
v___f_3167_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_3167_, 0, v_____do__lift_3165_);
lean_closure_set(v___f_3167_, 1, v_id_3160_);
lean_closure_set(v___f_3167_, 2, v_inst_3161_);
lean_closure_set(v___f_3167_, 3, v_inst_3162_);
lean_closure_set(v___f_3167_, 4, v___x_3163_);
v___x_3168_ = lean_apply_4(v_toBind_3164_, lean_box(0), lean_box(0), v_getOptions_3166_, v___f_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_id_3174_){
_start:
{
lean_object* v_toBind_3175_; lean_object* v_getEnv_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; 
v_toBind_3175_ = lean_ctor_get(v_inst_3170_, 1);
lean_inc_n(v_toBind_3175_, 2);
v_getEnv_3176_ = lean_ctor_get(v_inst_3171_, 0);
lean_inc(v_getEnv_3176_);
lean_dec_ref(v_inst_3171_);
v___x_3177_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___closed__0));
v___f_3178_ = lean_alloc_closure((void*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3178_, 0, v_inst_3172_);
lean_closure_set(v___f_3178_, 1, v_id_3174_);
lean_closure_set(v___f_3178_, 2, v_inst_3170_);
lean_closure_set(v___f_3178_, 3, v_inst_3173_);
lean_closure_set(v___f_3178_, 4, v___x_3177_);
lean_closure_set(v___f_3178_, 5, v_toBind_3175_);
v___x_3179_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v_getEnv_3176_, v___f_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe(lean_object* v_m_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_id_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___redArg(v_inst_3181_, v_inst_3182_, v_inst_3183_, v_inst_3184_, v_id_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0(lean_object* v_text_3187_, lean_object* v_hoverLine_3188_, lean_object* v_x_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 9)
{
lean_object* v_i_3192_; lean_object* v___x_3193_; 
v_i_3192_ = lean_ctor_get(v_x_3190_, 0);
v___x_3193_ = l_Lean_Elab_Info_pos_x3f(v_x_3190_);
if (lean_obj_tag(v___x_3193_) == 1)
{
lean_object* v_val_3194_; lean_object* v___x_3195_; 
v_val_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = l_Lean_Elab_Info_tailPos_x3f(v_x_3190_);
if (lean_obj_tag(v___x_3195_) == 1)
{
lean_object* v_val_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3211_; 
v_val_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3211_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_val_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3211_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v_line_3201_; uint8_t v___x_3202_; 
lean_inc_ref(v_text_3187_);
v___x_3200_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3187_, v_val_3194_);
lean_dec(v_val_3194_);
v_line_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_line_3201_);
lean_dec_ref(v___x_3200_);
v___x_3202_ = lean_nat_dec_le(v_line_3201_, v_hoverLine_3188_);
lean_dec(v_line_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_del_object(v___x_3198_);
lean_dec(v_val_3196_);
lean_dec_ref(v_text_3187_);
v___x_3203_ = lean_box(0);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; lean_object* v_line_3205_; uint8_t v___x_3206_; 
v___x_3204_ = l_Lean_FileMap_utf8PosToLspPos(v_text_3187_, v_val_3196_);
lean_dec(v_val_3196_);
v_line_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_line_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_nat_dec_le(v_hoverLine_3188_, v_line_3205_);
lean_dec(v_line_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
lean_del_object(v___x_3198_);
v___x_3207_ = lean_box(0);
return v___x_3207_;
}
else
{
lean_object* v___x_3209_; 
lean_inc_ref(v_i_3192_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v_i_3192_);
v___x_3209_ = v___x_3198_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_i_3192_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
else
{
lean_object* v___x_3212_; 
lean_dec(v___x_3195_);
lean_dec(v_val_3194_);
lean_dec_ref(v_text_3187_);
v___x_3212_ = lean_box(0);
return v___x_3212_;
}
}
else
{
lean_object* v___x_3213_; 
lean_dec(v___x_3193_);
lean_dec_ref(v_text_3187_);
v___x_3213_ = lean_box(0);
return v___x_3213_;
}
}
else
{
lean_object* v___x_3214_; 
lean_dec_ref(v_text_3187_);
v___x_3214_ = lean_box(0);
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed(lean_object* v_text_3215_, lean_object* v_hoverLine_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_, lean_object* v_x_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_Widget_widgetInfosAt_x3f___lam__0(v_text_3215_, v_hoverLine_3216_, v_x_3217_, v_x_3218_, v_x_3219_);
lean_dec_ref(v_x_3219_);
lean_dec_ref(v_x_3218_);
lean_dec_ref(v_x_3217_);
lean_dec(v_hoverLine_3216_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_widgetInfosAt_x3f(lean_object* v_text_3221_, lean_object* v_t_3222_, lean_object* v_hoverLine_3223_){
_start:
{
lean_object* v___f_3224_; lean_object* v___x_3225_; 
v___f_3224_ = lean_alloc_closure((void*)(l_Lean_Widget_widgetInfosAt_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_3224_, 0, v_text_3221_);
lean_closure_set(v___f_3224_, 1, v_hoverLine_3223_);
v___x_3225_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3224_, v_t_3222_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(lean_object* v_j_3226_, lean_object* v_k_3227_){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = l_Lean_Json_getObjValD(v_j_3226_, v_k_3227_);
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0___boxed(lean_object* v_j_3230_, lean_object* v_k_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_j_3230_, v_k_3231_);
lean_dec_ref(v_k_3231_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_x_3235_) == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1___closed__0));
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_x_3235_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(lean_object* v_j_3239_, lean_object* v_k_3240_){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = l_Lean_Json_getObjValD(v_j_3239_, v_k_3240_);
v___x_3242_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1_spec__1(v___x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1___boxed(lean_object* v_j_3243_, lean_object* v_k_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_j_3243_, v_k_3244_);
lean_dec_ref(v_k_3244_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(lean_object* v_json_3250_){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v_a_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v_a_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v_a_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3273_; 
v___x_3251_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc_n(v_json_3250_, 4);
v___x_3252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3250_, v___x_3251_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3255_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3250_, v___x_3254_);
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3258_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3250_, v___x_3257_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3261_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3250_, v___x_3260_);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref(v___x_3261_);
v___x_3263_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3264_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__1(v_json_3250_, v___x_3263_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3267_ = v___x_3264_;
v_isShared_3268_ = v_isSharedCheck_3273_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3273_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3269_, 0, v_a_3253_);
lean_ctor_set(v___x_3269_, 1, v_a_3256_);
lean_ctor_set(v___x_3269_, 2, v_a_3259_);
lean_ctor_set(v___x_3269_, 3, v_a_3262_);
lean_ctor_set(v___x_3269_, 4, v_a_3265_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v___x_3269_);
v___x_3271_ = v___x_3267_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(lean_object* v_k_3276_, lean_object* v_x_3277_){
_start:
{
if (lean_obj_tag(v_x_3277_) == 0)
{
lean_object* v___x_3278_; 
lean_dec_ref(v_k_3276_);
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
else
{
lean_object* v_val_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_val_3279_ = lean_ctor_get(v_x_3277_, 0);
lean_inc(v_val_3279_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_k_3276_);
lean_ctor_set(v___x_3280_, 1, v_val_3279_);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
return v___x_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0___boxed(lean_object* v_k_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v_k_3283_, v_x_3284_);
lean_dec(v_x_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(lean_object* v_x_3286_){
_start:
{
lean_object* v_id_3287_; lean_object* v_javascriptHash_3288_; lean_object* v_props_3289_; lean_object* v_range_x3f_3290_; lean_object* v_name_x3f_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_id_3287_ = lean_ctor_get(v_x_3286_, 0);
v_javascriptHash_3288_ = lean_ctor_get(v_x_3286_, 1);
v_props_3289_ = lean_ctor_get(v_x_3286_, 2);
v_range_x3f_3290_ = lean_ctor_get(v_x_3286_, 3);
v_name_x3f_3291_ = lean_ctor_get(v_x_3286_, 4);
v___x_3292_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_id_3287_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v_id_3287_);
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_javascriptHash_3288_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v_javascriptHash_3288_);
v___x_3298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v___x_3294_);
v___x_3299_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
lean_inc(v_props_3289_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v_props_3289_);
v___x_3301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3294_);
v___x_3302_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_));
v___x_3303_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v___x_3302_, v_range_x3f_3290_);
v___x_3304_ = ((lean_object*)(l_Lean_Widget_instToJsonUserWidgetDefinition_toJson___closed__0));
v___x_3305_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39__spec__0(v___x_3304_, v_name_x3f_3291_);
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v___x_3294_);
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3303_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3301_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3298_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3295_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3312_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3310_, v___x_3311_);
v___x_3313_ = l_Lean_Json_mkObj(v___x_3312_);
lean_dec(v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39____boxed(lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(v_x_3314_);
lean_dec_ref(v_x_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_toWidgetInstance_3320_; lean_object* v_range_x3f_3321_; lean_object* v_name_x3f_3322_; lean_object* v_id_3323_; uint64_t v_javascriptHash_3324_; lean_object* v_props_3325_; lean_object* v___x_3326_; lean_object* v_fst_3327_; lean_object* v_snd_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3368_; 
v_toWidgetInstance_3320_ = lean_ctor_get(v_a_3318_, 0);
lean_inc_ref(v_toWidgetInstance_3320_);
v_range_x3f_3321_ = lean_ctor_get(v_a_3318_, 1);
lean_inc(v_range_x3f_3321_);
v_name_x3f_3322_ = lean_ctor_get(v_a_3318_, 2);
lean_inc(v_name_x3f_3322_);
lean_dec_ref(v_a_3318_);
v_id_3323_ = lean_ctor_get(v_toWidgetInstance_3320_, 0);
lean_inc(v_id_3323_);
v_javascriptHash_3324_ = lean_ctor_get_uint64(v_toWidgetInstance_3320_, sizeof(void*)*2);
v_props_3325_ = lean_ctor_get(v_toWidgetInstance_3320_, 1);
lean_inc_ref(v_props_3325_);
lean_dec_ref(v_toWidgetInstance_3320_);
v___x_3326_ = lean_apply_1(v_props_3325_, v_a_3319_);
v_fst_3327_ = lean_ctor_get(v___x_3326_, 0);
v_snd_3328_ = lean_ctor_get(v___x_3326_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3330_ = v___x_3326_;
v_isShared_3331_ = v_isSharedCheck_3368_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_snd_3328_);
lean_inc(v_fst_3327_);
lean_dec(v___x_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3368_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___y_3338_; lean_object* v_fst_3339_; lean_object* v_snd_3340_; lean_object* v_fst_3347_; 
v___x_3332_ = 1;
v___x_3333_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_3323_, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
v___x_3335_ = lean_uint64_to_nat(v_javascriptHash_3324_);
v___x_3336_ = l_Lean_bignumToJson(v___x_3335_);
if (lean_obj_tag(v_range_x3f_3321_) == 0)
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_box(0);
v_fst_3347_ = v___x_3358_;
goto v___jp_3346_;
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3367_; 
v_val_3359_ = lean_ctor_get(v_range_x3f_3321_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_range_x3f_3321_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3361_ = v_range_x3f_3321_;
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_val_3359_);
lean_dec(v_range_x3f_3321_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_3359_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3363_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
v_fst_3347_ = v___x_3365_;
goto v___jp_3346_;
}
}
}
v___jp_3337_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3334_);
lean_ctor_set(v___x_3341_, 1, v___x_3336_);
lean_ctor_set(v___x_3341_, 2, v_fst_3327_);
lean_ctor_set(v___x_3341_, 3, v___y_3338_);
lean_ctor_set(v___x_3341_, 4, v_fst_3339_);
v___x_3342_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_39_(v___x_3341_);
lean_dec_ref_known(v___x_3341_, 5);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v_snd_3340_);
lean_ctor_set(v___x_3330_, 0, v___x_3342_);
v___x_3344_ = v___x_3330_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_snd_3340_);
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
if (lean_obj_tag(v_name_x3f_3322_) == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_box(0);
v___y_3338_ = v_fst_3347_;
v_fst_3339_ = v___x_3348_;
v_snd_3340_ = v_snd_3328_;
goto v___jp_3337_;
}
else
{
lean_object* v_val_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3357_; 
v_val_3349_ = lean_ctor_get(v_name_x3f_3322_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_name_x3f_3322_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3351_ = v_name_x3f_3322_;
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_val_3349_);
lean_dec(v_name_x3f_3322_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_val_3349_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3353_);
v___x_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
v___y_3338_ = v_fst_3347_;
v_fst_3339_ = v___x_3355_;
v_snd_3340_ = v_snd_3328_;
goto v___jp_3337_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_props_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_props_3369_);
lean_ctor_set(v___x_3371_, 1, v___y_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20_(v_j_3372_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v_id_3383_; lean_object* v_javascriptHash_3384_; lean_object* v_props_3385_; lean_object* v_range_x3f_3386_; lean_object* v_name_x3f_3387_; lean_object* v___x_3388_; 
v_a_3382_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3373_, 1);
v_id_3383_ = lean_ctor_get(v_a_3382_, 0);
lean_inc(v_id_3383_);
v_javascriptHash_3384_ = lean_ctor_get(v_a_3382_, 1);
lean_inc(v_javascriptHash_3384_);
v_props_3385_ = lean_ctor_get(v_a_3382_, 2);
lean_inc(v_props_3385_);
v_range_x3f_3386_ = lean_ctor_get(v_a_3382_, 3);
lean_inc(v_range_x3f_3386_);
v_name_x3f_3387_ = lean_ctor_get(v_a_3382_, 4);
lean_inc(v_name_x3f_3387_);
lean_dec(v_a_3382_);
v___x_3388_ = l_Lean_Name_fromJson_x3f(v_id_3383_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_name_x3f_3387_);
lean_dec(v_range_x3f_3386_);
lean_dec(v_props_3385_);
lean_dec(v_javascriptHash_3384_);
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3398_ = l_Lean_UInt64_fromJson_x3f(v_javascriptHash_3384_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3397_);
lean_dec(v_name_x3f_3387_);
lean_dec(v_range_x3f_3386_);
lean_dec(v_props_3385_);
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
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3461_; 
v_a_3407_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3409_ = v___x_3398_;
v_isShared_3410_ = v_isSharedCheck_3461_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3398_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3461_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___f_3411_; lean_object* v___y_3413_; lean_object* v_____do__lift_3414_; lean_object* v_____do__lift_3422_; 
v___f_3411_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_), 2, 1);
lean_closure_set(v___f_3411_, 0, v_props_3385_);
if (lean_obj_tag(v_range_x3f_3386_) == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
v_____do__lift_3422_ = v___x_3442_;
goto v___jp_3421_;
}
else
{
lean_object* v_val_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3460_; 
v_val_3443_ = lean_ctor_get(v_range_x3f_3386_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_range_x3f_3386_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3445_ = v_range_x3f_3386_;
v_isShared_3446_ = v_isSharedCheck_3460_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_val_3443_);
lean_dec(v_range_x3f_3386_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3460_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; 
v___x_3447_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_3443_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_del_object(v___x_3445_);
lean_dec_ref(v___f_3411_);
lean_del_object(v___x_3409_);
lean_dec(v_a_3407_);
lean_dec(v_a_3397_);
lean_dec(v_name_x3f_3387_);
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; 
v_a_3456_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3447_, 1);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v_a_3456_);
v___x_3458_ = v___x_3445_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
v_____do__lift_3422_ = v___x_3458_;
goto v___jp_3421_;
}
}
}
}
v___jp_3412_:
{
lean_object* v___x_3415_; uint64_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3415_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3415_, 0, v_a_3397_);
lean_ctor_set(v___x_3415_, 1, v___f_3411_);
v___x_3416_ = lean_unbox_uint64(v_a_3407_);
lean_dec(v_a_3407_);
lean_ctor_set_uint64(v___x_3415_, sizeof(void*)*2, v___x_3416_);
v___x_3417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___y_3413_);
lean_ctor_set(v___x_3417_, 2, v_____do__lift_3414_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3417_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
v___jp_3421_:
{
if (lean_obj_tag(v_name_x3f_3387_) == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_box(0);
v___y_3413_ = v_____do__lift_3422_;
v_____do__lift_3414_ = v___x_3423_;
goto v___jp_3412_;
}
else
{
lean_object* v_val_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3441_; 
v_val_3424_ = lean_ctor_get(v_name_x3f_3387_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_name_x3f_3387_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3426_ = v_name_x3f_3387_;
v_isShared_3427_ = v_isSharedCheck_3441_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_val_3424_);
lean_dec(v_name_x3f_3387_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3441_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Json_getStr_x3f(v_val_3424_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_del_object(v___x_3426_);
lean_dec(v_____do__lift_3422_);
lean_dec_ref(v___f_3411_);
lean_del_object(v___x_3409_);
lean_dec(v_a_3407_);
lean_dec(v_a_3397_);
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; 
v_a_3437_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3428_, 1);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v_a_3437_);
v___x_3439_ = v___x_3426_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
v___y_3413_ = v_____do__lift_3422_;
v_____do__lift_3414_ = v___x_3439_;
goto v___jp_3412_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(lean_object* v_j_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1____boxed(lean_object* v_j_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_j_3465_, v_a_3466_);
lean_dec_ref(v_a_3466_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(lean_object* v_json_3475_){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
v___x_3476_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3477_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_3273022877____hygCtx___hyg_20__spec__0(v_json_3475_, v___x_3476_);
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(lean_object* v_x_3488_){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3489_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_));
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v_x_3488_);
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3491_);
v___x_3494_ = ((lean_object*)(l_Lean_Widget_instToJsonGetWidgetSourceParams_toJson___closed__2));
v___x_3495_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonGetWidgetSourceParams_toJson_spec__0(v___x_3493_, v___x_3494_);
v___x_3496_ = l_Lean_Json_mkObj(v___x_3495_);
lean_dec(v___x_3495_);
return v___x_3496_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(size_t v_sz_3499_, size_t v_i_3500_, lean_object* v_bs_3501_){
_start:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_lt(v_i_3500_, v_sz_3499_);
if (v___x_3502_ == 0)
{
return v_bs_3501_;
}
else
{
lean_object* v_v_3503_; lean_object* v___x_3504_; lean_object* v_bs_x27_3505_; size_t v___x_3506_; size_t v___x_3507_; lean_object* v___x_3508_; 
v_v_3503_ = lean_array_uget(v_bs_3501_, v_i_3500_);
v___x_3504_ = lean_unsigned_to_nat(0u);
v_bs_x27_3505_ = lean_array_uset(v_bs_3501_, v_i_3500_, v___x_3504_);
v___x_3506_ = ((size_t)1ULL);
v___x_3507_ = lean_usize_add(v_i_3500_, v___x_3506_);
v___x_3508_ = lean_array_uset(v_bs_x27_3505_, v_i_3500_, v_v_3503_);
v_i_3500_ = v___x_3507_;
v_bs_3501_ = v___x_3508_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3499_ = stack[0].m_num;
size_t v_i_3500_ = stack[1].m_num;
lean_object* v_bs_3501_ = stack[2].m_obj;
lean_object* v_res_3510_;
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3499_, v_i_3500_, v_bs_3501_);
stack->m_obj
 = v_res_3510_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1___boxed(lean_object* v_sz_3511_, lean_object* v_i_3512_, lean_object* v_bs_3513_){
_start:
{
size_t v_sz_boxed_3514_; size_t v_i_boxed_3515_; lean_object* v_res_3516_; 
v_sz_boxed_3514_ = lean_unbox_usize(v_sz_3511_);
lean_dec(v_sz_3511_);
v_i_boxed_3515_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_boxed_3514_, v_i_boxed_3515_, v_bs_3513_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(lean_object* v_a_3517_){
_start:
{
size_t v_sz_3518_; size_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_sz_3518_ = lean_array_size(v_a_3517_);
v___x_3519_ = ((size_t)0ULL);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_spec__1(v_sz_3518_, v___x_3519_, v_a_3517_);
v___x_3521_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(size_t v_sz_3522_, size_t v_i_3523_, lean_object* v_bs_3524_, lean_object* v___y_3525_){
_start:
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_usize_dec_lt(v_i_3523_, v_sz_3522_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v_bs_3524_);
lean_ctor_set(v___x_3527_, 1, v___y_3525_);
return v___x_3527_;
}
else
{
lean_object* v_v_3528_; lean_object* v___x_3529_; lean_object* v_fst_3530_; lean_object* v_snd_3531_; lean_object* v___x_3532_; lean_object* v_bs_x27_3533_; size_t v___x_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
v_v_3528_ = lean_array_uget_borrowed(v_bs_3524_, v_i_3523_);
lean_inc(v_v_3528_);
v___x_3529_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_enc_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3528_, v___y_3525_);
v_fst_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_fst_3530_);
v_snd_3531_ = lean_ctor_get(v___x_3529_, 1);
lean_inc(v_snd_3531_);
lean_dec_ref(v___x_3529_);
v___x_3532_ = lean_unsigned_to_nat(0u);
v_bs_x27_3533_ = lean_array_uset(v_bs_3524_, v_i_3523_, v___x_3532_);
v___x_3534_ = ((size_t)1ULL);
v___x_3535_ = lean_usize_add(v_i_3523_, v___x_3534_);
v___x_3536_ = lean_array_uset(v_bs_x27_3533_, v_i_3523_, v_fst_3530_);
v_i_3523_ = v___x_3535_;
v_bs_3524_ = v___x_3536_;
v___y_3525_ = v_snd_3531_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3522_ = stack[0].m_num;
size_t v_i_3523_ = stack[1].m_num;
lean_object* v_bs_3524_ = stack[2].m_obj;
lean_object* v___y_3525_ = stack[3].m_obj;
lean_object* v_res_3538_;
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3522_, v_i_3523_, v_bs_3524_, v___y_3525_);
stack->m_obj
 = v_res_3538_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___boxed(lean_object* v_sz_3539_, lean_object* v_i_3540_, lean_object* v_bs_3541_, lean_object* v___y_3542_){
_start:
{
size_t v_sz_boxed_3543_; size_t v_i_boxed_3544_; lean_object* v_res_3545_; 
v_sz_boxed_3543_ = lean_unbox_usize(v_sz_3539_);
lean_dec(v_sz_3539_);
v_i_boxed_3544_ = lean_unbox_usize(v_i_3540_);
lean_dec(v_i_3540_);
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_boxed_3543_, v_i_boxed_3544_, v_bs_3541_, v___y_3542_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
size_t v_sz_3548_; size_t v___x_3549_; lean_object* v___x_3550_; lean_object* v_fst_3551_; lean_object* v_snd_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3561_; 
v_sz_3548_ = lean_array_size(v_a_3546_);
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_sz_3548_, v___x_3549_, v_a_3546_, v_a_3547_);
v_fst_3551_ = lean_ctor_get(v___x_3550_, 0);
v_snd_3552_ = lean_ctor_get(v___x_3550_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3554_ = v___x_3550_;
v_isShared_3555_ = v_isSharedCheck_3561_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_snd_3552_);
lean_inc(v_fst_3551_);
lean_dec(v___x_3550_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3561_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3556_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_fst_3551_);
v___x_3557_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_29_(v___x_3556_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3557_);
v___x_3559_ = v___x_3554_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_snd_3552_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(size_t v_sz_3562_, size_t v_i_3563_, lean_object* v_bs_3564_){
_start:
{
uint8_t v___x_3565_; 
v___x_3565_ = lean_usize_dec_lt(v_i_3563_, v_sz_3562_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_bs_3564_);
return v___x_3566_;
}
else
{
lean_object* v_v_3567_; lean_object* v___x_3568_; 
v_v_3567_ = lean_array_uget_borrowed(v_bs_3564_, v_i_3563_);
lean_inc(v_v_3567_);
v___x_3568_ = l_Lean_Widget_instRpcEncodablePanelWidgetInstance_dec___redArg_00___x40_Lean_Widget_UserWidget_3433604829____hygCtx___hyg_1_(v_v_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_bs_3564_);
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
lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v_bs_x27_3579_; size_t v___x_3580_; size_t v___x_3581_; lean_object* v___x_3582_; 
v_a_3577_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3578_ = lean_unsigned_to_nat(0u);
v_bs_x27_3579_ = lean_array_uset(v_bs_3564_, v_i_3563_, v___x_3578_);
v___x_3580_ = ((size_t)1ULL);
v___x_3581_ = lean_usize_add(v_i_3563_, v___x_3580_);
v___x_3582_ = lean_array_uset(v_bs_x27_3579_, v_i_3563_, v_a_3577_);
v_i_3563_ = v___x_3581_;
v_bs_3564_ = v___x_3582_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3562_ = stack[0].m_num;
size_t v_i_3563_ = stack[1].m_num;
lean_object* v_bs_3564_ = stack[2].m_obj;
lean_object* v_res_3584_;
v_res_3584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3562_, v_i_3563_, v_bs_3564_);
stack->m_obj
 = v_res_3584_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg___boxed(lean_object* v_sz_3585_, lean_object* v_i_3586_, lean_object* v_bs_3587_){
_start:
{
size_t v_sz_boxed_3588_; size_t v_i_boxed_3589_; lean_object* v_res_3590_; 
v_sz_boxed_3588_ = lean_unbox_usize(v_sz_3585_);
lean_dec(v_sz_3585_);
v_i_boxed_3589_ = lean_unbox_usize(v_i_3586_);
lean_dec(v_i_3586_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_boxed_3588_, v_i_boxed_3589_, v_bs_3587_);
return v_res_3590_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(size_t v_sz_3591_, size_t v_i_3592_, lean_object* v_bs_3593_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_lt(v_i_3592_, v_sz_3591_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_bs_3593_);
return v___x_3595_;
}
else
{
lean_object* v_v_3596_; lean_object* v___x_3597_; lean_object* v_bs_x27_3598_; size_t v___x_3599_; size_t v___x_3600_; lean_object* v___x_3601_; 
v_v_3596_ = lean_array_uget(v_bs_3593_, v_i_3592_);
v___x_3597_ = lean_unsigned_to_nat(0u);
v_bs_x27_3598_ = lean_array_uset(v_bs_3593_, v_i_3592_, v___x_3597_);
v___x_3599_ = ((size_t)1ULL);
v___x_3600_ = lean_usize_add(v_i_3592_, v___x_3599_);
v___x_3601_ = lean_array_uset(v_bs_x27_3598_, v_i_3592_, v_v_3596_);
v_i_3592_ = v___x_3600_;
v_bs_3593_ = v___x_3601_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3591_ = stack[0].m_num;
size_t v_i_3592_ = stack[1].m_num;
lean_object* v_bs_3593_ = stack[2].m_obj;
lean_object* v_res_3603_;
v_res_3603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3591_, v_i_3592_, v_bs_3593_);
stack->m_obj
 = v_res_3603_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_sz_3604_, lean_object* v_i_3605_, lean_object* v_bs_3606_){
_start:
{
size_t v_sz_boxed_3607_; size_t v_i_boxed_3608_; lean_object* v_res_3609_; 
v_sz_boxed_3607_ = lean_unbox_usize(v_sz_3604_);
lean_dec(v_sz_3604_);
v_i_boxed_3608_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_res_3609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_3607_, v_i_boxed_3608_, v_bs_3606_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(lean_object* v_x_3611_){
_start:
{
if (lean_obj_tag(v_x_3611_) == 4)
{
lean_object* v_elems_3612_; size_t v_sz_3613_; size_t v___x_3614_; lean_object* v___x_3615_; 
v_elems_3612_ = lean_ctor_get(v_x_3611_, 0);
lean_inc_ref(v_elems_3612_);
lean_dec_ref_known(v_x_3611_, 1);
v_sz_3613_ = lean_array_size(v_elems_3612_);
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0_spec__0(v_sz_3613_, v___x_3614_, v_elems_3612_);
return v___x_3615_;
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3616_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0___closed__0));
v___x_3617_ = lean_unsigned_to_nat(80u);
v___x_3618_ = l_Lean_Json_pretty(v_x_3611_, v___x_3617_);
v___x_3619_ = lean_string_append(v___x_3616_, v___x_3618_);
lean_dec_ref(v___x_3618_);
v___x_3620_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v___x_3621_ = lean_string_append(v___x_3619_, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(lean_object* v_j_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_UserWidget_629054736____hygCtx___hyg_10_(v_j_3623_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3635_; 
v_a_3634_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3625_, 1);
v___x_3635_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__0(v_a_3634_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
else
{
lean_object* v_a_3644_; size_t v_sz_3645_; size_t v___x_3646_; lean_object* v___x_3647_; 
v_a_3644_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3635_, 1);
v_sz_3645_ = lean_array_size(v_a_3644_);
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3645_, v___x_3646_, v_a_3644_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_a_3656_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3647_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3647_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1____boxed(lean_object* v_j_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_j_3664_, v_a_3665_);
lean_dec_ref(v_a_3665_);
return v_res_3666_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(size_t v_sz_3667_, size_t v_i_3668_, lean_object* v_bs_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___redArg(v_sz_3667_, v_i_3668_, v_bs_3669_);
return v___x_3671_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3667_ = stack[0].m_num;
size_t v_i_3668_ = stack[1].m_num;
lean_object* v_bs_3669_ = stack[2].m_obj;
lean_object* v___y_3670_ = stack[3].m_obj;
lean_object* v_res_3672_;
v_res_3672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_3667_, v_i_3668_, v_bs_3669_, v___y_3670_);
stack->m_obj
 = v_res_3672_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1___boxed(lean_object* v_sz_3673_, lean_object* v_i_3674_, lean_object* v_bs_3675_, lean_object* v___y_3676_){
_start:
{
size_t v_sz_boxed_3677_; size_t v_i_boxed_3678_; lean_object* v_res_3679_; 
v_sz_boxed_3677_ = lean_unbox_usize(v_sz_3673_);
lean_dec(v_sz_3673_);
v_i_boxed_3678_ = lean_unbox_usize(v_i_3674_);
lean_dec(v_i_3674_);
v_res_3679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableGetWidgetsResponse_dec_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1__spec__1(v_sz_boxed_3677_, v_i_boxed_3678_, v_bs_3675_, v___y_3676_);
lean_dec_ref(v___y_3676_);
return v_res_3679_;
}
}
lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(lean_object* v_x_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
if (lean_obj_tag(v_x_3686_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_a_3692_ = lean_ctor_get(v_x_3686_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v_x_3686_, 1);
v___x_3693_ = l_Lean_stringToMessageData(v_a_3692_);
v___x_3694_ = l_Lean_throwError___at___00Lean_throwAttrMustBeGlobal___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__4_spec__6___redArg(v___x_3693_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3694_;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
v_a_3695_ = lean_ctor_get(v_x_3686_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_x_3686_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v_x_3686_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v_x_3686_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 0);
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3686_ = stack[0].m_obj;
lean_object* v___y_3687_ = stack[1].m_obj;
lean_object* v___y_3688_ = stack[2].m_obj;
lean_object* v___y_3689_ = stack[3].m_obj;
lean_object* v___y_3690_ = stack[4].m_obj;
lean_object* v_res_3703_;
v_res_3703_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
stack->m_obj
 = v_res_3703_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg___boxed(lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3710_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(lean_object* v_id_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; lean_object* v_env_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3717_ = lean_st_ref_get(v___y_3715_);
v_env_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc_ref(v_env_3718_);
lean_dec(v___x_3717_);
v___x_3719_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3714_);
v___x_3720_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3721_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3718_, v___x_3719_, v___x_3720_, v_id_3711_);
lean_dec_ref(v___x_3719_);
v___x_3722_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v___x_3721_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3722_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3711_ = stack[0].m_obj;
lean_object* v___y_3712_ = stack[1].m_obj;
lean_object* v___y_3713_ = stack[2].m_obj;
lean_object* v___y_3714_ = stack[3].m_obj;
lean_object* v___y_3715_ = stack[4].m_obj;
lean_object* v_res_3723_;
v_res_3723_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
stack->m_obj
 = v_res_3723_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0___boxed(lean_object* v_id_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
return v_res_3730_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(lean_object* v___x_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_bs_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_usize_dec_lt(v_i_3733_, v_sz_3732_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v___x_3731_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_bs_3734_);
return v___x_3741_;
}
else
{
lean_object* v_v_3742_; lean_object* v_id_3743_; lean_object* v___x_3744_; lean_object* v_bs_x27_3745_; lean_object* v_a_3747_; lean_object* v___y_3757_; uint8_t v___x_3778_; lean_object* v___x_3779_; 
v_v_3742_ = lean_array_uget(v_bs_3734_, v_i_3733_);
v_id_3743_ = lean_ctor_get(v_v_3742_, 0);
v___x_3744_ = lean_unsigned_to_nat(0u);
v_bs_x27_3745_ = lean_array_uset(v_bs_3734_, v_i_3733_, v___x_3744_);
v___x_3778_ = 0;
lean_inc(v_id_3743_);
lean_inc_ref(v___x_3731_);
v___x_3779_ = l_Lean_Environment_find_x3f(v___x_3731_, v_id_3743_, v___x_3778_);
if (lean_obj_tag(v___x_3779_) == 0)
{
v___y_3757_ = v___x_3779_;
goto v___jp_3756_;
}
else
{
lean_object* v_val_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_val_3780_ = lean_ctor_get(v___x_3779_, 0);
v___x_3781_ = l_Lean_ConstantInfo_type(v_val_3780_);
v___x_3782_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3783_ = l_Lean_Expr_isConstOf(v___x_3781_, v___x_3782_);
lean_dec_ref(v___x_3781_);
if (v___x_3783_ == 0)
{
lean_dec_ref_known(v___x_3779_, 1);
goto v___jp_3754_;
}
else
{
v___y_3757_ = v___x_3779_;
goto v___jp_3756_;
}
}
v___jp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; size_t v___x_3750_; size_t v___x_3751_; lean_object* v___x_3752_; 
v___x_3748_ = lean_box(0);
v___x_3749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3749_, 0, v_v_3742_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
lean_ctor_set(v___x_3749_, 2, v_a_3747_);
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_add(v_i_3733_, v___x_3750_);
v___x_3752_ = lean_array_uset(v_bs_x27_3745_, v_i_3733_, v___x_3749_);
v_i_3733_ = v___x_3751_;
v_bs_3734_ = v___x_3752_;
goto _start;
}
v___jp_3754_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_box(0);
v_a_3747_ = v___x_3755_;
goto v___jp_3746_;
}
v___jp_3756_:
{
if (lean_obj_tag(v___y_3757_) == 0)
{
goto v___jp_3754_;
}
else
{
lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3776_; 
v_isSharedCheck_3776_ = !lean_is_exclusive(v___y_3757_);
if (v_isSharedCheck_3776_ == 0)
{
lean_object* v_unused_3777_; 
v_unused_3777_ = lean_ctor_get(v___y_3757_, 0);
lean_dec(v_unused_3777_);
v___x_3759_ = v___y_3757_;
v_isShared_3760_ = v_isSharedCheck_3776_;
goto v_resetjp_3758_;
}
else
{
lean_dec(v___y_3757_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3776_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_id_3761_; lean_object* v___x_3762_; 
v_id_3761_ = lean_ctor_get(v_v_3742_, 0);
lean_inc(v_id_3761_);
v___x_3762_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3761_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v_name_3764_; lean_object* v___x_3766_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
v_name_3764_ = lean_ctor_get(v_a_3763_, 0);
lean_inc_ref(v_name_3764_);
lean_dec(v_a_3763_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_name_3764_);
v___x_3766_ = v___x_3759_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_name_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
v_a_3747_ = v___x_3766_;
goto v___jp_3746_;
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_del_object(v___x_3759_);
lean_dec_ref(v_bs_x27_3745_);
lean_dec(v_v_3742_);
lean_dec_ref(v___x_3731_);
v_a_3768_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3762_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3762_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3731_ = stack[0].m_obj;
size_t v_sz_3732_ = stack[1].m_num;
size_t v_i_3733_ = stack[2].m_num;
lean_object* v_bs_3734_ = stack[3].m_obj;
lean_object* v___y_3735_ = stack[4].m_obj;
lean_object* v___y_3736_ = stack[5].m_obj;
lean_object* v___y_3737_ = stack[6].m_obj;
lean_object* v___y_3738_ = stack[7].m_obj;
lean_object* v_res_3784_;
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3731_, v_sz_3732_, v_i_3733_, v_bs_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
stack->m_obj
 = v_res_3784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1___boxed(lean_object* v___x_3785_, lean_object* v_sz_3786_, lean_object* v_i_3787_, lean_object* v_bs_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
size_t v_sz_boxed_3794_; size_t v_i_boxed_3795_; lean_object* v_res_3796_; 
v_sz_boxed_3794_ = lean_unbox_usize(v_sz_3786_);
lean_dec(v_sz_3786_);
v_i_boxed_3795_ = lean_unbox_usize(v_i_3787_);
lean_dec(v_i_3787_);
v_res_3796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v___x_3785_, v_sz_boxed_3794_, v_i_boxed_3795_, v_bs_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3796_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(lean_object* v___x_3797_, lean_object* v___x_3798_, size_t v_sz_3799_, size_t v_i_3800_, lean_object* v_bs_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_usize_dec_lt(v_i_3800_, v_sz_3799_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; 
lean_dec_ref(v___x_3798_);
lean_dec_ref(v___x_3797_);
v___x_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_bs_3801_);
return v___x_3808_;
}
else
{
lean_object* v_v_3809_; lean_object* v_toWidgetInstance_3810_; lean_object* v_stx_3811_; lean_object* v_id_3812_; lean_object* v___x_3813_; lean_object* v_bs_x27_3814_; lean_object* v___y_3816_; lean_object* v___y_3817_; uint8_t v___x_3823_; lean_object* v_a_3825_; lean_object* v___y_3840_; lean_object* v___x_3860_; 
v_v_3809_ = lean_array_uget_borrowed(v_bs_3801_, v_i_3800_);
v_toWidgetInstance_3810_ = lean_ctor_get(v_v_3809_, 0);
lean_inc_ref(v_toWidgetInstance_3810_);
v_stx_3811_ = lean_ctor_get(v_v_3809_, 1);
lean_inc(v_stx_3811_);
v_id_3812_ = lean_ctor_get(v_toWidgetInstance_3810_, 0);
v___x_3813_ = lean_unsigned_to_nat(0u);
v_bs_x27_3814_ = lean_array_uset(v_bs_3801_, v_i_3800_, v___x_3813_);
v___x_3823_ = 0;
lean_inc(v_id_3812_);
lean_inc_ref(v___x_3798_);
v___x_3860_ = l_Lean_Environment_find_x3f(v___x_3798_, v_id_3812_, v___x_3823_);
if (lean_obj_tag(v___x_3860_) == 0)
{
v___y_3840_ = v___x_3860_;
goto v___jp_3839_;
}
else
{
lean_object* v_val_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_val_3861_ = lean_ctor_get(v___x_3860_, 0);
v___x_3862_ = l_Lean_ConstantInfo_type(v_val_3861_);
v___x_3863_ = ((lean_object*)(l_Lean_Widget_instFromJsonUserWidgetDefinition_fromJson___closed__1));
v___x_3864_ = l_Lean_Expr_isConstOf(v___x_3862_, v___x_3863_);
lean_dec_ref(v___x_3862_);
if (v___x_3864_ == 0)
{
lean_dec_ref_known(v___x_3860_, 1);
goto v___jp_3837_;
}
else
{
v___y_3840_ = v___x_3860_;
goto v___jp_3839_;
}
}
v___jp_3815_:
{
lean_object* v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3818_, 0, v_toWidgetInstance_3810_);
lean_ctor_set(v___x_3818_, 1, v___y_3817_);
lean_ctor_set(v___x_3818_, 2, v___y_3816_);
v___x_3819_ = ((size_t)1ULL);
v___x_3820_ = lean_usize_add(v_i_3800_, v___x_3819_);
v___x_3821_ = lean_array_uset(v_bs_x27_3814_, v_i_3800_, v___x_3818_);
v_i_3800_ = v___x_3820_;
v_bs_3801_ = v___x_3821_;
goto _start;
}
v___jp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_Syntax_getRange_x3f(v_stx_3811_, v___x_3823_);
lean_dec(v_stx_3811_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_box(0);
v___y_3816_ = v_a_3825_;
v___y_3817_ = v___x_3827_;
goto v___jp_3815_;
}
else
{
lean_object* v_val_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3836_; 
v_val_3828_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3830_ = v___x_3826_;
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_val_3828_);
lean_dec(v___x_3826_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_inc_ref(v___x_3797_);
v___x_3832_ = l_Lean_Syntax_Range_toLspRange(v___x_3797_, v_val_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3832_);
v___x_3834_ = v___x_3830_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
v___y_3816_ = v_a_3825_;
v___y_3817_ = v___x_3834_;
goto v___jp_3815_;
}
}
}
}
v___jp_3837_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_box(0);
v_a_3825_ = v___x_3838_;
goto v___jp_3824_;
}
v___jp_3839_:
{
if (lean_obj_tag(v___y_3840_) == 0)
{
goto v___jp_3837_;
}
else
{
lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3858_; 
v_isSharedCheck_3858_ = !lean_is_exclusive(v___y_3840_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v___y_3840_, 0);
lean_dec(v_unused_3859_);
v___x_3842_ = v___y_3840_;
v_isShared_3843_ = v_isSharedCheck_3858_;
goto v_resetjp_3841_;
}
else
{
lean_dec(v___y_3840_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3858_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; 
lean_inc(v_id_3812_);
v___x_3844_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0(v_id_3812_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v_name_3846_; lean_object* v___x_3848_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v_name_3846_ = lean_ctor_get(v_a_3845_, 0);
lean_inc_ref(v_name_3846_);
lean_dec(v_a_3845_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v_name_3846_);
v___x_3848_ = v___x_3842_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_name_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
v_a_3825_ = v___x_3848_;
goto v___jp_3824_;
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_del_object(v___x_3842_);
lean_dec_ref(v_bs_x27_3814_);
lean_dec(v_stx_3811_);
lean_dec_ref(v_toWidgetInstance_3810_);
lean_dec_ref(v___x_3798_);
lean_dec_ref(v___x_3797_);
v_a_3850_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3844_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3844_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3797_ = stack[0].m_obj;
lean_object* v___x_3798_ = stack[1].m_obj;
size_t v_sz_3799_ = stack[2].m_num;
size_t v_i_3800_ = stack[3].m_num;
lean_object* v_bs_3801_ = stack[4].m_obj;
lean_object* v___y_3802_ = stack[5].m_obj;
lean_object* v___y_3803_ = stack[6].m_obj;
lean_object* v___y_3804_ = stack[7].m_obj;
lean_object* v___y_3805_ = stack[8].m_obj;
lean_object* v_res_3865_;
v_res_3865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3797_, v___x_3798_, v_sz_3799_, v_i_3800_, v_bs_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
stack->m_obj
 = v_res_3865_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2___boxed(lean_object* v___x_3866_, lean_object* v___x_3867_, lean_object* v_sz_3868_, lean_object* v_i_3869_, lean_object* v_bs_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
size_t v_sz_boxed_3876_; size_t v_i_boxed_3877_; lean_object* v_res_3878_; 
v_sz_boxed_3876_ = lean_unbox_usize(v_sz_3868_);
lean_dec(v_sz_3868_);
v_i_boxed_3877_ = lean_unbox_usize(v_i_3869_);
lean_dec(v_i_3869_);
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v___x_3866_, v___x_3867_, v_sz_boxed_3876_, v_i_boxed_3877_, v_bs_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
return v_res_3878_;
}
}
lean_object* l_Lean_Widget_getWidgets___lam__0(lean_object* v_pos_3879_, lean_object* v_text_3880_, lean_object* v_val_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; lean_object* v_env_3888_; lean_object* v___x_3889_; 
v___x_3887_ = lean_st_ref_get(v___y_3885_);
v_env_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc_ref(v_env_3888_);
lean_dec(v___x_3887_);
v___x_3889_ = l_Lean_Widget_evalPanelWidgets(v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; size_t v_sz_3891_; size_t v___x_3892_; lean_object* v___x_3893_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v_sz_3891_ = lean_array_size(v_a_3890_);
v___x_3892_ = ((size_t)0ULL);
lean_inc_ref(v_env_3888_);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__1(v_env_3888_, v_sz_3891_, v___x_3892_, v_a_3890_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v_line_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; size_t v_sz_3898_; lean_object* v___x_3899_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v_line_3895_ = lean_ctor_get(v_pos_3879_, 0);
lean_inc(v_line_3895_);
lean_dec_ref(v_pos_3879_);
lean_inc_ref(v_text_3880_);
v___x_3896_ = l_Lean_Widget_widgetInfosAt_x3f(v_text_3880_, v_val_3881_, v_line_3895_);
v___x_3897_ = lean_array_mk(v___x_3896_);
v_sz_3898_ = lean_array_size(v___x_3897_);
v___x_3899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_getWidgets_spec__2(v_text_3880_, v_env_3888_, v_sz_3898_, v___x_3892_, v___x_3897_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3908_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3908_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3908_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3904_ = l_Array_append___redArg(v_a_3894_, v_a_3900_);
lean_dec(v_a_3900_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3904_);
v___x_3906_ = v___x_3902_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec(v_a_3894_);
v_a_3909_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3899_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3899_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref(v_env_3888_);
lean_dec_ref(v_val_3881_);
lean_dec_ref(v_text_3880_);
lean_dec_ref(v_pos_3879_);
v_a_3917_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3893_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3893_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_env_3888_);
lean_dec_ref(v_val_3881_);
lean_dec_ref(v_text_3880_);
lean_dec_ref(v_pos_3879_);
v_a_3925_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3889_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3889_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pos_3879_ = stack[0].m_obj;
lean_object* v_text_3880_ = stack[1].m_obj;
lean_object* v_val_3881_ = stack[2].m_obj;
lean_object* v___y_3882_ = stack[3].m_obj;
lean_object* v___y_3883_ = stack[4].m_obj;
lean_object* v___y_3884_ = stack[5].m_obj;
lean_object* v___y_3885_ = stack[6].m_obj;
lean_object* v_res_3933_;
v_res_3933_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3879_, v_text_3880_, v_val_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
stack->m_obj
 = v_res_3933_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__0___boxed(lean_object* v_pos_3934_, lean_object* v_text_3935_, lean_object* v_val_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_Widget_getWidgets___lam__0(v_pos_3934_, v_text_3935_, v_val_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3942_;
}
}
lean_object* l_Lean_Widget_getWidgets___lam__1(lean_object* v_pos_3947_, lean_object* v_text_3948_, lean_object* v_x_3949_, lean_object* v___y_3950_){
_start:
{
if (lean_obj_tag(v_x_3949_) == 1)
{
lean_object* v_val_3955_; 
v_val_3955_ = lean_ctor_get(v_x_3949_, 0);
lean_inc(v_val_3955_);
lean_dec_ref_known(v_x_3949_, 1);
if (lean_obj_tag(v_val_3955_) == 0)
{
lean_object* v_i_3956_; 
v_i_3956_ = lean_ctor_get(v_val_3955_, 0);
if (lean_obj_tag(v_i_3956_) == 0)
{
lean_object* v_info_3957_; lean_object* v___f_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_info_3957_ = lean_ctor_get(v_i_3956_, 0);
lean_inc_ref(v_info_3957_);
v___f_3958_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3958_, 0, v_pos_3947_);
lean_closure_set(v___f_3958_, 1, v_text_3948_);
lean_closure_set(v___f_3958_, 2, v_val_3955_);
v___x_3959_ = lean_box(0);
v___x_3960_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__1));
v___x_3961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3961_, 0, v_info_3957_);
lean_ctor_set(v___x_3961_, 1, v___x_3959_);
lean_ctor_set(v___x_3961_, 2, v___x_3960_);
v___x_3962_ = lean_obj_once(&l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_, &l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__once, _init_l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___lam__3___closed__1_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2_);
v___x_3963_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_3961_, v___x_3962_, v___f_3958_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3980_; 
v_a_3972_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3974_ = v___x_3963_;
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3963_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = l_Lean_Server_RequestError_ofIoError(v_a_3972_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3976_);
v___x_3978_ = v___x_3974_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_dec_ref_known(v_val_3955_, 2);
lean_dec_ref(v_text_3948_);
lean_dec_ref(v_pos_3947_);
goto v___jp_3952_;
}
}
else
{
lean_dec(v_val_3955_);
lean_dec_ref(v_text_3948_);
lean_dec_ref(v_pos_3947_);
goto v___jp_3952_;
}
}
else
{
lean_dec(v_x_3949_);
lean_dec_ref(v_text_3948_);
lean_dec_ref(v_pos_3947_);
goto v___jp_3952_;
}
v___jp_3952_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = ((lean_object*)(l_Lean_Widget_getWidgets___lam__1___closed__0));
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
return v___x_3954_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgets___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pos_3947_ = stack[0].m_obj;
lean_object* v_text_3948_ = stack[1].m_obj;
lean_object* v_x_3949_ = stack[2].m_obj;
lean_object* v___y_3950_ = stack[3].m_obj;
lean_object* v_res_3981_;
v_res_3981_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3947_, v_text_3948_, v_x_3949_, v___y_3950_);
stack->m_obj
 = v_res_3981_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___lam__1___boxed(lean_object* v_pos_3982_, lean_object* v_text_3983_, lean_object* v_x_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Widget_getWidgets___lam__1(v_pos_3982_, v_text_3983_, v_x_3984_, v___y_3985_);
lean_dec_ref(v___y_3985_);
return v_res_3987_;
}
}
lean_object* l_Lean_Widget_getWidgets(lean_object* v_pos_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v_a_3992_; lean_object* v_toEditableDocumentCore_3993_; lean_object* v_meta_3994_; lean_object* v_initSnap_3995_; lean_object* v_text_3996_; lean_object* v___f_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3991_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Widget_getWidgetSource_spec__0(v_a_3989_);
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref(v___x_3991_);
v_toEditableDocumentCore_3993_ = lean_ctor_get(v_a_3992_, 0);
lean_inc_ref(v_toEditableDocumentCore_3993_);
lean_dec(v_a_3992_);
v_meta_3994_ = lean_ctor_get(v_toEditableDocumentCore_3993_, 0);
lean_inc_ref(v_meta_3994_);
v_initSnap_3995_ = lean_ctor_get(v_toEditableDocumentCore_3993_, 1);
lean_inc_ref(v_initSnap_3995_);
lean_dec_ref(v_toEditableDocumentCore_3993_);
v_text_3996_ = lean_ctor_get(v_meta_3994_, 3);
lean_inc_ref_n(v_text_3996_, 2);
lean_dec_ref(v_meta_3994_);
lean_inc_ref(v_pos_3988_);
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_Widget_getWidgets___lam__1___boxed), 5, 2);
lean_closure_set(v___f_3997_, 0, v_pos_3988_);
lean_closure_set(v___f_3997_, 1, v_text_3996_);
v___x_3998_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3996_, v_pos_3988_);
v___x_3999_ = 1;
v___x_4000_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_3995_, v_text_3996_, v___x_3998_, v___x_3999_);
v___x_4001_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4000_, v___f_3997_, v_a_3989_);
return v___x_4001_;
}
}
LEAN_EXPORT void l_Lean_Widget_getWidgets_0interp(lean_interpreter_value* stack)
{
lean_object* v_pos_3988_ = stack[0].m_obj;
lean_object* v_a_3989_ = stack[1].m_obj;
lean_object* v_res_4002_;
v_res_4002_ = l_Lean_Widget_getWidgets(v_pos_3988_, v_a_3989_);
stack->m_obj
 = v_res_4002_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_getWidgets___boxed(lean_object* v_pos_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Widget_getWidgets(v_pos_4003_, v_a_4004_);
lean_dec_ref(v_a_4004_);
return v_res_4006_;
}
}
lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_object* v_00_u03b1_4007_, lean_object* v_x_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___redArg(v_x_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4008_ = stack[1].m_obj;
lean_object* v___y_4009_ = stack[2].m_obj;
lean_object* v___y_4010_ = stack[3].m_obj;
lean_object* v___y_4011_ = stack[4].m_obj;
lean_object* v___y_4012_ = stack[5].m_obj;
lean_object* v_res_4015_;
v_res_4015_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(lean_box(0), v_x_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
stack->m_obj
 = v_res_4015_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4016_, lean_object* v_x_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_ofExcept___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_evalUserWidgetDefinitionUnsafe___at___00Lean_Widget_getWidgets_spec__0_spec__0(v_00_u03b1_4016_, v_x_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4023_;
}
}
lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(lean_object* v_val_4024_, lean_object* v___f_4025_, lean_object* v_x_4026_, lean_object* v___y_4027_){
_start:
{
if (lean_obj_tag(v_x_4026_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v___f_4025_);
v_a_4029_ = lean_ctor_get(v_x_4026_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_x_4026_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v_x_4026_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v_x_4026_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set_tag(v___x_4031_, 1);
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4053_; 
v_a_4037_ = lean_ctor_get(v_x_4026_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_x_4026_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4039_ = v_x_4026_;
v_isShared_4040_ = v_isSharedCheck_4053_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v_x_4026_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4053_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4041_; lean_object* v_objects_4042_; lean_object* v_expireTime_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v_fst_4047_; lean_object* v_snd_4048_; lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4041_ = lean_st_ref_take(v_val_4024_);
v_objects_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_ref(v_objects_4042_);
v_expireTime_4043_ = lean_ctor_get(v___x_4041_, 1);
lean_inc(v_expireTime_4043_);
lean_dec(v___x_4041_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_4044_, 0, v_expireTime_4043_);
v___x_4045_ = l_Lean_Widget_instRpcEncodableGetWidgetsResponse_enc_00___x40_Lean_Widget_UserWidget_577854155____hygCtx___hyg_1_(v_a_4037_, v_objects_4042_);
v___x_4046_ = l_Prod_map___redArg(v___f_4025_, v___f_4044_, v___x_4045_);
v_fst_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_fst_4047_);
v_snd_4048_ = lean_ctor_get(v___x_4046_, 1);
lean_inc(v_snd_4048_);
lean_dec_ref(v___x_4046_);
v___x_4049_ = lean_st_ref_put(v_val_4024_, v_snd_4048_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set_tag(v___x_4039_, 0);
lean_ctor_set(v___x_4039_, 0, v_fst_4047_);
v___x_4051_ = v___x_4039_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_fst_4047_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_4024_ = stack[0].m_obj;
lean_object* v___f_4025_ = stack[1].m_obj;
lean_object* v_x_4026_ = stack[2].m_obj;
lean_object* v___y_4027_ = stack[3].m_obj;
lean_object* v_res_4054_;
v_res_4054_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_4024_, v___f_4025_, v_x_4026_, v___y_4027_);
stack->m_obj
 = v_res_4054_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed(lean_object* v_val_4055_, lean_object* v___f_4056_, lean_object* v_x_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2(v_val_4055_, v___f_4056_, v_x_4057_, v___y_4058_);
lean_dec_ref(v___y_4058_);
lean_dec(v_val_4055_);
return v_res_4060_;
}
}
lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(lean_object* v___f_4061_, lean_object* v_method_4062_, lean_object* v_handler_4063_, uint64_t v_seshId_4064_, lean_object* v_j_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_rpcSessions_4068_; lean_object* v___x_4069_; 
v_rpcSessions_4068_ = lean_ctor_get(v___y_4066_, 0);
v___x_4069_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_1579414551____hygCtx___hyg_2__spec__2___redArg(v_rpcSessions_4068_, v_seshId_4064_);
if (lean_obj_tag(v___x_4069_) == 1)
{
lean_object* v_val_4070_; lean_object* v___f_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_val_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc_n(v_val_4070_, 2);
lean_dec_ref_known(v___x_4069_, 1);
v___f_4071_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4071_, 0, v_val_4070_);
lean_closure_set(v___f_4071_, 1, v___f_4061_);
v___x_4072_ = lean_st_ref_get(v_val_4070_);
lean_dec(v_val_4070_);
lean_dec(v___x_4072_);
lean_inc(v_j_4065_);
v___x_4073_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v_j_4065_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v___f_4071_);
lean_dec_ref(v_handler_4063_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4094_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4094_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
uint8_t v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4092_; 
v___x_4078_ = 3;
v___x_4079_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__0));
v___x_4080_ = 1;
v___x_4081_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_4062_, v___x_4080_);
v___x_4082_ = lean_string_append(v___x_4079_, v___x_4081_);
lean_dec_ref(v___x_4081_);
v___x_4083_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__1));
v___x_4084_ = lean_string_append(v___x_4082_, v___x_4083_);
v___x_4085_ = l_Lean_Json_compress(v_j_4065_);
v___x_4086_ = lean_string_append(v___x_4084_, v___x_4085_);
lean_dec_ref(v___x_4085_);
v___x_4087_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__2));
v___x_4088_ = lean_string_append(v___x_4086_, v___x_4087_);
v___x_4089_ = lean_string_append(v___x_4088_, v_a_4074_);
lean_dec(v_a_4074_);
v___x_4090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
lean_ctor_set_uint8(v___x_4090_, sizeof(void*)*1, v___x_4078_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set_tag(v___x_4076_, 1);
lean_ctor_set(v___x_4076_, 0, v___x_4090_);
v___x_4092_ = v___x_4076_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4096_; 
lean_dec(v_j_4065_);
lean_dec(v_method_4062_);
v_a_4095_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4073_, 1);
lean_inc_ref(v___y_4066_);
v___x_4096_ = lean_apply_3(v_handler_4063_, v_a_4095_, v___y_4066_, lean_box(0));
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___x_4098_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
v___x_4098_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_a_4097_, v___f_4071_, v___y_4066_);
return v___x_4098_;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec_ref(v___f_4071_);
v_a_4099_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4096_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4096_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec(v___x_4069_);
lean_dec(v_j_4065_);
lean_dec_ref(v_handler_4063_);
lean_dec(v_method_4062_);
lean_dec_ref(v___f_4061_);
v___x_4107_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___lam__3___closed__4));
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
}
LEAN_EXPORT void l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4061_ = stack[0].m_obj;
lean_object* v_method_4062_ = stack[1].m_obj;
lean_object* v_handler_4063_ = stack[2].m_obj;
uint64_t v_seshId_4064_ = stack[3].m_num;
lean_object* v_j_4065_ = stack[4].m_obj;
lean_object* v___y_4066_ = stack[5].m_obj;
lean_object* v_res_4109_;
v_res_4109_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v___f_4061_, v_method_4062_, v_handler_4063_, v_seshId_4064_, v_j_4065_, v___y_4066_);
stack->m_obj
 = v_res_4109_;
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v___f_4110_, lean_object* v_method_4111_, lean_object* v_handler_4112_, lean_object* v_seshId_4113_, lean_object* v_j_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint64_t v_seshId_boxed_4117_; lean_object* v_res_4118_; 
v_seshId_boxed_4117_ = lean_unbox_uint64(v_seshId_4113_);
lean_dec_ref(v_seshId_4113_);
v_res_4118_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0(v___f_4110_, v_method_4111_, v_handler_4112_, v_seshId_boxed_4117_, v_j_4114_, v___y_4115_);
lean_dec_ref(v___y_4115_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_4119_, lean_object* v_handler_4120_){
_start:
{
lean_object* v___f_4121_; lean_object* v___f_4122_; 
v___f_4121_ = ((lean_object*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__1___closed__0));
v___f_4122_ = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4122_, 0, v___f_4121_);
lean_closure_set(v___f_4122_, 1, v_method_4119_);
lean_closure_set(v___f_4122_, 2, v_handler_4120_);
return v___f_4122_;
}
}
lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(lean_object* v_method_4123_, lean_object* v_handler_4124_){
_start:
{
lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v_errMsg_4131_; uint8_t v___x_4132_; 
v___x_4126_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__0));
v___x_4127_ = 1;
lean_inc(v_method_4123_);
v___x_4128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_4123_, v___x_4127_);
v___x_4129_ = lean_string_append(v___x_4126_, v___x_4128_);
lean_dec_ref(v___x_4128_);
v___x_4130_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__1));
v_errMsg_4131_ = lean_string_append(v___x_4129_, v___x_4130_);
v___x_4132_ = l_Lean_initializing();
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec_ref(v_handler_4124_);
lean_dec(v_method_4123_);
v___x_4133_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__2));
v___x_4134_ = lean_string_append(v_errMsg_4131_, v___x_4133_);
v___x_4135_ = lean_mk_io_user_error(v___x_4134_);
v___x_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_4137_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
v___x_4138_ = lean_st_ref_get(v___x_4137_);
v___x_4139_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4138_, v_method_4123_);
lean_dec(v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec_ref(v_errMsg_4131_);
lean_inc(v_method_4123_);
v___x_4140_ = l_Lean_Server_wrapRpcProcedure___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_spec__0(v_method_4123_, v_handler_4124_);
v___x_4141_ = lean_st_ref_take(v___x_4137_);
v___x_4142_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4141_, v_method_4123_, v___x_4140_);
v___x_4143_ = lean_st_ref_put(v___x_4137_, v___x_4142_);
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
else
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec_ref(v_handler_4124_);
lean_dec(v_method_4123_);
v___x_4145_ = ((lean_object*)(l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_2369312278____hygCtx___hyg_2__spec__0___closed__3));
v___x_4146_ = lean_string_append(v_errMsg_4131_, v___x_4145_);
v___x_4147_ = lean_mk_io_user_error(v___x_4146_);
v___x_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_4123_ = stack[0].m_obj;
lean_object* v_handler_4124_ = stack[1].m_obj;
lean_object* v_res_4149_;
v_res_4149_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_4123_, v_handler_4124_);
stack->m_obj
 = v_res_4149_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4150_, lean_object* v_handler_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v_method_4150_, v_handler_4151_);
return v_res_4153_;
}
}
lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4161_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4162_ = ((lean_object*)(l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_));
v___x_4163_ = l_Lean_Server_registerBuiltinRpcProcedure___at___00__private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__spec__0(v___x_4161_, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4164_;
v_res_4164_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2____boxed(lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_initFn_00___x40_Lean_Widget_UserWidget_915949662____hygCtx___hyg_2_();
return v_res_4166_;
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
