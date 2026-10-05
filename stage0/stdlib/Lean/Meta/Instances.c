// Lean compiler output
// Module: Lean.Meta.Instances
// Imports: public import Init.Data.Range.Polymorphic.Stream public import Lean.Meta.DiscrTree.Main public import Lean.Meta.CollectMVars import Lean.Meta.PPBinder import Lean.Util.UnusedBinders import Lean.Meta.CollectFVars import Init.While import Lean.OriginalConstKind import Lean.ProjFns
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
uint8_t l_Lean_wasOriginallyDefn(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_ppAsBinder(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "synthInstance"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkSynthOrder"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(239, 153, 166, 25, 45, 140, 142, 203)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 121, 149, 143, 151, 161, 209, 111)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "check that instances do not introduce metavariable in non-out-params"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(210, 135, 61, 136, 69, 26, 61, 117)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 212, 166, 255, 222, 243, 240, 184)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthInstance_checkSynthOrder;
static const lean_array_object l_Lean_Meta_instInhabitedInstanceEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedInstanceEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__0_value;
static const lean_string_object l_Lean_Meta_instInhabitedInstanceEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_instInhabitedInstanceEntry_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedInstanceEntry_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_instInhabitedInstanceEntry_default___closed__2 = (const lean_object*)&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInstanceEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInstanceEntry;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqInstanceEntry___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqInstanceEntry___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqInstanceEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqInstanceEntry___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqInstanceEntry___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqInstanceEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqInstanceEntry = (const lean_object*)&l_Lean_Meta_instBEqInstanceEntry___closed__0_value;
static const lean_string_object l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<local>"};
static const lean_object* l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatInstanceEntry___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_instToFormatInstanceEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instToFormatInstanceEntry___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instToFormatInstanceEntry___closed__0 = (const lean_object*)&l_Lean_Meta_instToFormatInstanceEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instToFormatInstanceEntry = (const lean_object*)&l_Lean_Meta_instToFormatInstanceEntry___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInstances_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInstances;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Instances_erase___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Instances_erase___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Instances_erase___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Instances_erase___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Instances_erase___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Instances_erase___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Instances_erase___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Instances_erase___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Instances_erase___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Instances_erase___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Instances_erase___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Instances_erase___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` does not have [instance] attribute"};
static const lean_object* l_Lean_Meta_Instances_erase___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Instances_erase___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Instances_erase___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Instances_erase___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instanceExtension"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 253, 187, 89, 234, 162, 232, 19)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instanceExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "semiOutParam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 187, 140, 108, 143, 232, 13, 120)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "cannot find synthesization order for instance "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " with type"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "\nall remaining arguments have metavariables:"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "synthOrder"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 119, 89, 231, 199, 121, 219, 201)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "synthesizing the arguments of "};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " in the order "};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "instance does not provide concrete values for (semi-)out-params"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "argument "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ": `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = " that cannot be inferred using typeclass synthesis. Specifically\n"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 176, .m_capacity = 176, .m_length = 175, .m_data = "\n\nThese arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis."};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5;
static const lean_array_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_value),((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "This instance has "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " argument"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_checkNonClassInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "The declaration `"};
static const lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_checkNonClassInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_checkNonClassInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` should not be an instance as its return type `"};
static const lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_checkNonClassInstance___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_checkNonClassInstance___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a type class."};
static const lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_checkNonClassInstance___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__0 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "classDefReducibility"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__1 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 250, 156, 61, 219, 107, 141, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 199, 74, 147, 156, 95, 99, 180)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__2 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__3 = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__3_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_addInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instance `"};
static const lean_object* l_Lean_Meta_addInstance___closed__0 = (const lean_object*)&l_Lean_Meta_addInstance___closed__0_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__1;
static const lean_string_object l_Lean_Meta_addInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` must be marked with `@[expose]`"};
static const lean_object* l_Lean_Meta_addInstance___closed__2 = (const lean_object*)&l_Lean_Meta_addInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__3;
static const lean_string_object l_Lean_Meta_addInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Definition `"};
static const lean_object* l_Lean_Meta_addInstance___closed__4 = (const lean_object*)&l_Lean_Meta_addInstance___closed__4_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__5;
static const lean_string_object l_Lean_Meta_addInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 274, .m_capacity = 274, .m_length = 273, .m_data = "` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this\ndefinition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`."};
static const lean_object* l_Lean_Meta_addInstance___closed__6 = (const lean_object*)&l_Lean_Meta_addInstance___closed__6_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Instances"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 69, 223, 114, 12, 235, 248, 125)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(245, 103, 148, 95, 163, 61, 86, 28)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(96, 213, 176, 90, 5, 29, 4, 245)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 119, 91, 79, 218, 216, 4, 30)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 34, 109, 117, 86, 219, 202, 202)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 31, 67, 74, 73, 155, 87, 189)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(245, 214, 117, 3, 115, 221, 181, 118)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(189, 44, 126, 187, 224, 191, 65, 145)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 189, 251, 134, 243, 7, 213, 15)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1841422150) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(243, 241, 116, 150, 66, 138, 129, 211)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 60, 149, 187, 173, 41, 226, 214)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(108, 138, 222, 169, 203, 203, 201, 186)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(213, 64, 26, 184, 137, 94, 159, 191)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 216, 85, 168, 141, 176, 253, 81)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "type class instance"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 427, .m_capacity = 427, .m_length = 426, .m_data = "Registers type class instances.\n\nThe `instance` command, which expands to `@[instance] def`, is usually preferred over using this\nattribute directly. However it might sometimes still be necessary to use this attribute directly,\nin particular for `opaque` instances.\n\nTo assign priorities to instances, `@[instance prio]` can be used (where `prio` is a priority).\nThis corresponds to the `instance (priority := prio)` notation."};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedDefaultInstances_default = (const lean_object*)&l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedDefaultInstances = (const lean_object*)&l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "defaultInstanceExtension"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 56, 120, 160, 178, 206, 131, 123)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addDefaultInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_defaultInstanceExtension;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid default instance `"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`, it has type `("};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " ...)`, but `"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a type class"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`, type must be of the form `(C ...)` where `C` is a type class"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),((lean_object*)(((size_t)(397728026) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(222, 44, 186, 211, 61, 97, 170, 158)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 145, 23, 81, 211, 60, 112, 222)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 144, 67, 128, 102, 189, 169, 9)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 200, 215, 58, 149, 211, 154, 152)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "default_instance"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 85, 15, 3, 86, 102, 227, 255)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "type class default instance"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = ((lean_object*)(l_Lean_Meta_instInhabitedInstanceEntry_default___closed__2));
v___x_66_ = l_Lean_Expr_const___override(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4(void){
_start:
{
uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_67_ = 0;
v___x_68_ = lean_box(0);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3, &l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3_once, _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__3);
v___x_71_ = ((lean_object*)(l_Lean_Meta_instInhabitedInstanceEntry_default___closed__0));
v___x_72_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
lean_ctor_set(v___x_72_, 3, v___x_68_);
lean_ctor_set(v___x_72_, 4, v___x_71_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*5, v___x_67_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry_default(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4, &l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstanceEntry_default___closed__4);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstanceEntry(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_instInhabitedInstanceEntry_default;
return v___x_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqInstanceEntry___lam__0(lean_object* v_e_u2081_75_, lean_object* v_e_u2082_76_){
_start:
{
lean_object* v_val_77_; lean_object* v_val_78_; uint8_t v___x_79_; 
v_val_77_ = lean_ctor_get(v_e_u2081_75_, 1);
v_val_78_ = lean_ctor_get(v_e_u2082_76_, 1);
v___x_79_ = lean_expr_eqv(v_val_77_, v_val_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqInstanceEntry___lam__0___boxed(lean_object* v_e_u2081_80_, lean_object* v_e_u2082_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_Meta_instBEqInstanceEntry___lam__0(v_e_u2081_80_, v_e_u2082_81_);
lean_dec_ref(v_e_u2082_81_);
lean_dec_ref(v_e_u2081_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatInstanceEntry___lam__0(lean_object* v_e_89_){
_start:
{
lean_object* v_globalName_x3f_90_; 
v_globalName_x3f_90_ = lean_ctor_get(v_e_89_, 3);
lean_inc(v_globalName_x3f_90_);
lean_dec_ref(v_e_89_);
if (lean_obj_tag(v_globalName_x3f_90_) == 1)
{
lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v_val_91_ = lean_ctor_get(v_globalName_x3f_90_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_globalName_x3f_90_);
if (v_isSharedCheck_100_ == 0)
{
v___x_93_ = v_globalName_x3f_90_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_dec(v_globalName_x3f_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_95_ = 1;
v___x_96_ = l_Lean_Name_toString(v_val_91_, v___x_95_);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 3);
lean_ctor_set(v___x_93_, 0, v___x_96_);
v___x_98_ = v___x_93_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v___x_101_; 
lean_dec(v_globalName_x3f_90_);
v___x_101_ = ((lean_object*)(l_Lean_Meta_instToFormatInstanceEntry___lam__0___closed__1));
return v___x_101_;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_104_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg(){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__1);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg();
return v_res_110_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg();
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_object* v_00_u03b2_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__2(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0);
v___x_118_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__1, &l_Lean_Meta_instInhabitedInstances_default___closed__1_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__1);
v___x_119_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__0, &l_Lean_Meta_instInhabitedInstances_default___closed__0_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__0);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_instInhabitedInstances_default;
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10_spec__18___redArg(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_ks_127_; lean_object* v_vs_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_152_; 
v_ks_127_ = lean_ctor_get(v_x_123_, 0);
v_vs_128_ = lean_ctor_get(v_x_123_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_123_);
if (v_isSharedCheck_152_ == 0)
{
v___x_130_ = v_x_123_;
v_isShared_131_ = v_isSharedCheck_152_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_vs_128_);
lean_inc(v_ks_127_);
lean_dec(v_x_123_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_152_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_array_get_size(v_ks_127_);
v___x_133_ = lean_nat_dec_lt(v_x_124_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
lean_dec(v_x_124_);
v___x_134_ = lean_array_push(v_ks_127_, v_x_125_);
v___x_135_ = lean_array_push(v_vs_128_, v_x_126_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_135_);
lean_ctor_set(v___x_130_, 0, v___x_134_);
v___x_137_ = v___x_130_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
else
{
lean_object* v_k_x27_139_; uint8_t v___x_140_; 
v_k_x27_139_ = lean_array_fget_borrowed(v_ks_127_, v_x_124_);
v___x_140_ = lean_name_eq(v_x_125_, v_k_x27_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_142_; 
if (v_isShared_131_ == 0)
{
v___x_142_ = v___x_130_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_ks_127_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_vs_128_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_x_124_, v___x_143_);
lean_dec(v_x_124_);
v_x_123_ = v___x_142_;
v_x_124_ = v___x_144_;
goto _start;
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_array_fset(v_ks_127_, v_x_124_, v_x_125_);
v___x_148_ = lean_array_fset(v_vs_128_, v_x_124_, v_x_126_);
lean_dec(v_x_124_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_148_);
lean_ctor_set(v___x_130_, 0, v___x_147_);
v___x_150_ = v___x_130_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_n_153_, lean_object* v_k_154_, lean_object* v_v_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10_spec__18___redArg(v_n_153_, v___x_156_, v_k_154_, v_v_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object* v_x_159_, size_t v_x_160_, size_t v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v_es_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v_j_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_es_164_ = lean_ctor_get(v_x_159_, 0);
v___x_165_ = ((size_t)31ULL);
v___x_166_ = lean_usize_land(v_x_160_, v___x_165_);
v_j_167_ = lean_usize_to_nat(v___x_166_);
v___x_168_ = lean_array_get_size(v_es_164_);
v___x_169_ = lean_nat_dec_lt(v_j_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec(v_j_167_);
lean_dec(v_x_163_);
lean_dec(v_x_162_);
return v_x_159_;
}
else
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_208_; 
lean_inc_ref(v_es_164_);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_x_159_, 0);
lean_dec(v_unused_209_);
v___x_171_ = v_x_159_;
v_isShared_172_ = v_isSharedCheck_208_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_x_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_208_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_v_173_; lean_object* v___x_174_; lean_object* v_xs_x27_175_; lean_object* v___y_177_; 
v_v_173_ = lean_array_fget(v_es_164_, v_j_167_);
v___x_174_ = lean_box(0);
v_xs_x27_175_ = lean_array_fset(v_es_164_, v_j_167_, v___x_174_);
switch(lean_obj_tag(v_v_173_))
{
case 0:
{
lean_object* v_key_182_; lean_object* v_val_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_193_; 
v_key_182_ = lean_ctor_get(v_v_173_, 0);
v_val_183_ = lean_ctor_get(v_v_173_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_v_173_);
if (v_isSharedCheck_193_ == 0)
{
v___x_185_ = v_v_173_;
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_val_183_);
lean_inc(v_key_182_);
lean_dec(v_v_173_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_name_eq(v_x_162_, v_key_182_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_del_object(v___x_185_);
v___x_188_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_182_, v_val_183_, v_x_162_, v_x_163_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___y_177_ = v___x_189_;
goto v___jp_176_;
}
else
{
lean_object* v___x_191_; 
lean_dec(v_val_183_);
lean_dec(v_key_182_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v_x_163_);
lean_ctor_set(v___x_185_, 0, v_x_162_);
v___x_191_ = v___x_185_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_x_162_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_x_163_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
v___y_177_ = v___x_191_;
goto v___jp_176_;
}
}
}
}
case 1:
{
lean_object* v_node_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_206_; 
v_node_194_ = lean_ctor_get(v_v_173_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_v_173_);
if (v_isSharedCheck_206_ == 0)
{
v___x_196_ = v_v_173_;
v_isShared_197_ = v_isSharedCheck_206_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_node_194_);
lean_dec(v_v_173_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_206_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_198_ = ((size_t)5ULL);
v___x_199_ = lean_usize_shift_right(v_x_160_, v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_add(v_x_161_, v___x_200_);
v___x_202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_node_194_, v___x_199_, v___x_201_, v_x_162_, v_x_163_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_202_);
v___x_204_ = v___x_196_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
v___y_177_ = v___x_204_;
goto v___jp_176_;
}
}
}
default: 
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v_x_162_);
lean_ctor_set(v___x_207_, 1, v_x_163_);
v___y_177_ = v___x_207_;
goto v___jp_176_;
}
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_array_fset(v_xs_x27_175_, v_j_167_, v___y_177_);
lean_dec(v_j_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_178_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
else
{
lean_object* v_ks_210_; lean_object* v_vs_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_229_; 
v_ks_210_ = lean_ctor_get(v_x_159_, 0);
v_vs_211_ = lean_ctor_get(v_x_159_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_229_ == 0)
{
v___x_213_ = v_x_159_;
v_isShared_214_ = v_isSharedCheck_229_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_vs_211_);
lean_inc(v_ks_210_);
lean_dec(v_x_159_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_229_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_ks_210_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_vs_211_);
v___x_216_ = v_reuseFailAlloc_228_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v_newNode_217_; size_t v___x_218_; uint8_t v___x_219_; 
v_newNode_217_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v___x_216_, v_x_162_, v_x_163_);
v___x_218_ = ((size_t)7ULL);
v___x_219_ = lean_usize_dec_le(v___x_218_, v_x_161_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_220_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_217_);
v___x_221_ = lean_unsigned_to_nat(4u);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
lean_dec(v___x_220_);
if (v___x_222_ == 0)
{
lean_object* v_ks_223_; lean_object* v_vs_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_ks_223_ = lean_ctor_get(v_newNode_217_, 0);
lean_inc_ref(v_ks_223_);
v_vs_224_ = lean_ctor_get(v_newNode_217_, 1);
lean_inc_ref(v_vs_224_);
lean_dec_ref(v_newNode_217_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg(v_x_161_, v_ks_223_, v_vs_224_, v___x_225_, v___x_226_);
lean_dec_ref(v_vs_224_);
lean_dec_ref(v_ks_223_);
return v___x_227_;
}
else
{
return v_newNode_217_;
}
}
else
{
return v_newNode_217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg(size_t v_depth_230_, lean_object* v_keys_231_, lean_object* v_vals_232_, lean_object* v_i_233_, lean_object* v_entries_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_keys_231_);
v___x_236_ = lean_nat_dec_lt(v_i_233_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_i_233_);
return v_entries_234_;
}
else
{
lean_object* v_k_237_; lean_object* v_v_238_; uint64_t v___y_240_; 
v_k_237_ = lean_array_fget_borrowed(v_keys_231_, v_i_233_);
v_v_238_ = lean_array_fget_borrowed(v_vals_232_, v_i_233_);
if (lean_obj_tag(v_k_237_) == 0)
{
uint64_t v___x_251_; 
v___x_251_ = 1723ULL;
v___y_240_ = v___x_251_;
goto v___jp_239_;
}
else
{
uint64_t v_hash_252_; 
v_hash_252_ = lean_ctor_get_uint64(v_k_237_, sizeof(void*)*2);
v___y_240_ = v_hash_252_;
goto v___jp_239_;
}
v___jp_239_:
{
size_t v_h_241_; size_t v___x_242_; lean_object* v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v_h_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_h_241_ = lean_uint64_to_usize(v___y_240_);
v___x_242_ = ((size_t)5ULL);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v_depth_230_, v___x_244_);
v___x_246_ = lean_usize_mul(v___x_242_, v___x_245_);
v_h_247_ = lean_usize_shift_right(v_h_241_, v___x_246_);
v___x_248_ = lean_nat_add(v_i_233_, v___x_243_);
lean_dec(v_i_233_);
lean_inc(v_v_238_);
lean_inc(v_k_237_);
v___x_249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_entries_234_, v_h_247_, v_depth_230_, v_k_237_, v_v_238_);
v_i_233_ = v___x_248_;
v_entries_234_ = v___x_249_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_depth_253_, lean_object* v_keys_254_, lean_object* v_vals_255_, lean_object* v_i_256_, lean_object* v_entries_257_){
_start:
{
size_t v_depth_boxed_258_; lean_object* v_res_259_; 
v_depth_boxed_258_ = lean_unbox_usize(v_depth_253_);
lean_dec(v_depth_253_);
v_res_259_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg(v_depth_boxed_258_, v_keys_254_, v_vals_255_, v_i_256_, v_entries_257_);
lean_dec_ref(v_vals_255_);
lean_dec_ref(v_keys_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
size_t v_x_3101__boxed_265_; size_t v_x_3102__boxed_266_; lean_object* v_res_267_; 
v_x_3101__boxed_265_ = lean_unbox_usize(v_x_261_);
lean_dec(v_x_261_);
v_x_3102__boxed_266_ = lean_unbox_usize(v_x_262_);
lean_dec(v_x_262_);
v_res_267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_260_, v_x_3101__boxed_265_, v_x_3102__boxed_266_, v_x_263_, v_x_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
uint64_t v___y_272_; 
if (lean_obj_tag(v_x_269_) == 0)
{
uint64_t v___x_276_; 
v___x_276_ = 1723ULL;
v___y_272_ = v___x_276_;
goto v___jp_271_;
}
else
{
uint64_t v_hash_277_; 
v_hash_277_ = lean_ctor_get_uint64(v_x_269_, sizeof(void*)*2);
v___y_272_ = v_hash_277_;
goto v___jp_271_;
}
v___jp_271_:
{
size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_uint64_to_usize(v___y_272_);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_268_, v___x_273_, v___x_274_, v_x_269_, v_x_270_);
return v___x_275_;
}
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_msg_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0);
v___x_281_ = lean_panic_fn_borrowed(v___x_280_, v_msg_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14_spec__17___redArg(lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
lean_object* v_ks_286_; lean_object* v_vs_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_311_; 
v_ks_286_ = lean_ctor_get(v_x_282_, 0);
v_vs_287_ = lean_ctor_get(v_x_282_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_311_ == 0)
{
v___x_289_ = v_x_282_;
v_isShared_290_ = v_isSharedCheck_311_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_vs_287_);
lean_inc(v_ks_286_);
lean_dec(v_x_282_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_311_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_ks_286_);
v___x_292_ = lean_nat_dec_lt(v_x_283_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v_x_283_);
v___x_293_ = lean_array_push(v_ks_286_, v_x_284_);
v___x_294_ = lean_array_push(v_vs_287_, v_x_285_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_294_);
lean_ctor_set(v___x_289_, 0, v___x_293_);
v___x_296_ = v___x_289_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v_k_x27_298_; uint8_t v___x_299_; 
v_k_x27_298_ = lean_array_fget_borrowed(v_ks_286_, v_x_283_);
v___x_299_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_284_, v_k_x27_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_301_; 
if (v_isShared_290_ == 0)
{
v___x_301_ = v___x_289_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_ks_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_vs_287_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_x_283_, v___x_302_);
lean_dec(v_x_283_);
v_x_282_ = v___x_301_;
v_x_283_ = v___x_303_;
goto _start;
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = lean_array_fset(v_ks_286_, v_x_283_, v_x_284_);
v___x_307_ = lean_array_fset(v_vs_287_, v_x_283_, v_x_285_);
lean_dec(v_x_283_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_307_);
lean_ctor_set(v___x_289_, 0, v___x_306_);
v___x_309_ = v___x_289_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(lean_object* v_n_312_, lean_object* v_k_313_, lean_object* v_v_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14_spec__17___redArg(v_n_312_, v___x_315_, v_k_313_, v_v_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(lean_object* v_x_317_, size_t v_x_318_, size_t v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_es_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v_j_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_es_322_ = lean_ctor_get(v_x_317_, 0);
v___x_323_ = ((size_t)31ULL);
v___x_324_ = lean_usize_land(v_x_318_, v___x_323_);
v_j_325_ = lean_usize_to_nat(v___x_324_);
v___x_326_ = lean_array_get_size(v_es_322_);
v___x_327_ = lean_nat_dec_lt(v_j_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_dec(v_j_325_);
lean_dec(v_x_321_);
lean_dec(v_x_320_);
return v_x_317_;
}
else
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_es_322_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_x_317_, 0);
lean_dec(v_unused_367_);
v___x_329_ = v_x_317_;
v_isShared_330_ = v_isSharedCheck_366_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_x_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_366_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_v_331_; lean_object* v___x_332_; lean_object* v_xs_x27_333_; lean_object* v___y_335_; 
v_v_331_ = lean_array_fget(v_es_322_, v_j_325_);
v___x_332_ = lean_box(0);
v_xs_x27_333_ = lean_array_fset(v_es_322_, v_j_325_, v___x_332_);
switch(lean_obj_tag(v_v_331_))
{
case 0:
{
lean_object* v_key_340_; lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
v_key_340_ = lean_ctor_get(v_v_331_, 0);
v_val_341_ = lean_ctor_get(v_v_331_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_v_331_);
if (v_isSharedCheck_351_ == 0)
{
v___x_343_ = v_v_331_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_inc(v_key_340_);
lean_dec(v_v_331_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_320_, v_key_340_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_del_object(v___x_343_);
v___x_346_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_340_, v_val_341_, v_x_320_, v_x_321_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___y_335_ = v___x_347_;
goto v___jp_334_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_val_341_);
lean_dec(v_key_340_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v_x_321_);
lean_ctor_set(v___x_343_, 0, v_x_320_);
v___x_349_ = v___x_343_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_x_320_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_x_321_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v___y_335_ = v___x_349_;
goto v___jp_334_;
}
}
}
}
case 1:
{
lean_object* v_node_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
v_node_352_ = lean_ctor_get(v_v_331_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_v_331_);
if (v_isSharedCheck_364_ == 0)
{
v___x_354_ = v_v_331_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_node_352_);
lean_dec(v_v_331_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_356_ = ((size_t)5ULL);
v___x_357_ = lean_usize_shift_right(v_x_318_, v___x_356_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_x_319_, v___x_358_);
v___x_360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(v_node_352_, v___x_357_, v___x_359_, v_x_320_, v_x_321_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_360_);
v___x_362_ = v___x_354_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v___y_335_ = v___x_362_;
goto v___jp_334_;
}
}
}
default: 
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_x_320_);
lean_ctor_set(v___x_365_, 1, v_x_321_);
v___y_335_ = v___x_365_;
goto v___jp_334_;
}
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_array_fset(v_xs_x27_333_, v_j_325_, v___y_335_);
lean_dec(v_j_325_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_336_);
v___x_338_ = v___x_329_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_ks_368_; lean_object* v_vs_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_387_; 
v_ks_368_ = lean_ctor_get(v_x_317_, 0);
v_vs_369_ = lean_ctor_get(v_x_317_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_387_ == 0)
{
v___x_371_ = v_x_317_;
v_isShared_372_ = v_isSharedCheck_387_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_vs_369_);
lean_inc(v_ks_368_);
lean_dec(v_x_317_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_387_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_ks_368_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_vs_369_);
v___x_374_ = v_reuseFailAlloc_386_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v_newNode_375_; size_t v___x_376_; uint8_t v___x_377_; 
v_newNode_375_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(v___x_374_, v_x_320_, v_x_321_);
v___x_376_ = ((size_t)7ULL);
v___x_377_ = lean_usize_dec_le(v___x_376_, v_x_319_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_375_);
v___x_379_ = lean_unsigned_to_nat(4u);
v___x_380_ = lean_nat_dec_lt(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
if (v___x_380_ == 0)
{
lean_object* v_ks_381_; lean_object* v_vs_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_ks_381_ = lean_ctor_get(v_newNode_375_, 0);
lean_inc_ref(v_ks_381_);
v_vs_382_ = lean_ctor_get(v_newNode_375_, 1);
lean_inc_ref(v_vs_382_);
lean_dec_ref(v_newNode_375_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg(v_x_319_, v_ks_381_, v_vs_382_, v___x_383_, v___x_384_);
lean_dec_ref(v_vs_382_);
lean_dec_ref(v_ks_381_);
return v___x_385_;
}
else
{
return v_newNode_375_;
}
}
else
{
return v_newNode_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg(size_t v_depth_388_, lean_object* v_keys_389_, lean_object* v_vals_390_, lean_object* v_i_391_, lean_object* v_entries_392_){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_array_get_size(v_keys_389_);
v___x_394_ = lean_nat_dec_lt(v_i_391_, v___x_393_);
if (v___x_394_ == 0)
{
lean_dec(v_i_391_);
return v_entries_392_;
}
else
{
lean_object* v_k_395_; lean_object* v_v_396_; uint64_t v___x_397_; size_t v_h_398_; size_t v___x_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v_h_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_k_395_ = lean_array_fget_borrowed(v_keys_389_, v_i_391_);
v_v_396_ = lean_array_fget_borrowed(v_vals_390_, v_i_391_);
v___x_397_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_395_);
v_h_398_ = lean_uint64_to_usize(v___x_397_);
v___x_399_ = ((size_t)5ULL);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_sub(v_depth_388_, v___x_401_);
v___x_403_ = lean_usize_mul(v___x_399_, v___x_402_);
v_h_404_ = lean_usize_shift_right(v_h_398_, v___x_403_);
v___x_405_ = lean_nat_add(v_i_391_, v___x_400_);
lean_dec(v_i_391_);
lean_inc(v_v_396_);
lean_inc(v_k_395_);
v___x_406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(v_entries_392_, v_h_404_, v_depth_388_, v_k_395_, v_v_396_);
v_i_391_ = v___x_405_;
v_entries_392_ = v___x_406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg___boxed(lean_object* v_depth_408_, lean_object* v_keys_409_, lean_object* v_vals_410_, lean_object* v_i_411_, lean_object* v_entries_412_){
_start:
{
size_t v_depth_boxed_413_; lean_object* v_res_414_; 
v_depth_boxed_413_ = lean_unbox_usize(v_depth_408_);
lean_dec(v_depth_408_);
v_res_414_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg(v_depth_boxed_413_, v_keys_409_, v_vals_410_, v_i_411_, v_entries_412_);
lean_dec_ref(v_vals_410_);
lean_dec_ref(v_keys_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_x_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
size_t v_x_3355__boxed_420_; size_t v_x_3356__boxed_421_; lean_object* v_res_422_; 
v_x_3355__boxed_420_ = lean_unbox_usize(v_x_416_);
lean_dec(v_x_416_);
v_x_3356__boxed_421_ = lean_unbox_usize(v_x_417_);
lean_dec(v_x_417_);
v_res_422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(v_x_415_, v_x_3355__boxed_420_, v_x_3356__boxed_421_, v_x_418_, v_x_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object* v_xs_423_, lean_object* v_v_424_, lean_object* v_i_425_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_array_get_size(v_xs_423_);
v___x_427_ = lean_nat_dec_lt(v_i_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_i_425_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
else
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_array_fget_borrowed(v_xs_423_, v_i_425_);
v___x_430_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_429_, v_v_424_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_add(v_i_425_, v___x_431_);
lean_dec(v_i_425_);
v_i_425_ = v___x_432_;
goto _start;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_i_425_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___boxed(lean_object* v_xs_435_, lean_object* v_v_436_, lean_object* v_i_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(v_xs_435_, v_v_436_, v_i_437_);
lean_dec(v_v_436_);
lean_dec_ref(v_xs_435_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object* v_xs_439_, lean_object* v_v_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(v_xs_439_, v_v_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object* v_xs_443_, lean_object* v_v_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(v_xs_443_, v_v_444_);
lean_dec(v_v_444_);
lean_dec_ref(v_xs_443_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_fst_448_; lean_object* v_fst_449_; uint8_t v___x_450_; 
v_fst_448_ = lean_ctor_get(v_a_446_, 0);
v_fst_449_ = lean_ctor_get(v_b_447_, 0);
v___x_450_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_448_, v_fst_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_a_451_, v_b_452_);
lean_dec_ref(v_b_452_);
lean_dec_ref(v_a_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v___x_455_, lean_object* v_as_456_, lean_object* v_k_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_mid_462_; lean_object* v_midVal_463_; uint8_t v___x_464_; 
v___x_460_ = lean_nat_add(v_x_458_, v_x_459_);
v___x_461_ = lean_unsigned_to_nat(1u);
v_mid_462_ = lean_nat_shiftr(v___x_460_, v___x_461_);
lean_dec(v___x_460_);
v_midVal_463_ = lean_array_fget_borrowed(v_as_456_, v_mid_462_);
v___x_464_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_midVal_463_, v_k_457_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
lean_dec(v_x_459_);
v___x_465_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_457_, v_midVal_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
lean_dec(v_x_458_);
v___x_466_ = lean_array_get_size(v_as_456_);
v___x_467_ = lean_nat_dec_lt(v_mid_462_, v___x_466_);
if (v___x_467_ == 0)
{
lean_dec(v_mid_462_);
lean_dec_ref(v___x_455_);
return v_as_456_;
}
else
{
lean_object* v___x_468_; lean_object* v_xs_x27_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v_xs_x27_469_ = lean_array_fset(v_as_456_, v_mid_462_, v___x_468_);
v___x_470_ = lean_array_fset(v_xs_x27_469_, v_mid_462_, v___x_455_);
lean_dec(v_mid_462_);
return v___x_470_;
}
}
else
{
v_x_459_ = v_mid_462_;
goto _start;
}
}
else
{
uint8_t v___x_472_; 
v___x_472_ = lean_nat_dec_eq(v_mid_462_, v_x_458_);
if (v___x_472_ == 0)
{
lean_dec(v_x_458_);
v_x_458_ = v_mid_462_;
goto _start;
}
else
{
lean_object* v___x_474_; lean_object* v_j_475_; lean_object* v_as_476_; lean_object* v___x_477_; 
lean_dec(v_mid_462_);
lean_dec(v_x_459_);
v___x_474_ = lean_nat_add(v_x_458_, v___x_461_);
lean_dec(v_x_458_);
v_j_475_ = lean_array_get_size(v_as_456_);
v_as_476_ = lean_array_push(v_as_456_, v___x_455_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_474_, v_as_476_, v_j_475_);
lean_dec(v___x_474_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v___x_478_, lean_object* v_as_479_, lean_object* v_k_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v___x_478_, v_as_479_, v_k_480_, v_x_481_, v_x_482_);
lean_dec_ref(v_k_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v___x_484_, lean_object* v_as_485_, lean_object* v_k_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_array_get_size(v_as_485_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_nat_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_fget_borrowed(v_as_485_, v___x_488_);
v___x_491_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_486_, v___x_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_490_, v_k_486_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_lt(v___x_488_, v___x_487_);
if (v___x_493_ == 0)
{
lean_dec_ref(v___x_484_);
return v_as_485_;
}
else
{
lean_object* v___x_494_; lean_object* v_xs_x27_495_; lean_object* v___x_496_; 
v___x_494_ = lean_box(0);
v_xs_x27_495_ = lean_array_fset(v_as_485_, v___x_488_, v___x_494_);
v___x_496_ = lean_array_fset(v_xs_x27_495_, v___x_488_, v___x_484_);
return v___x_496_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_sub(v___x_487_, v___x_497_);
v___x_499_ = lean_array_fget_borrowed(v_as_485_, v___x_498_);
v___x_500_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_499_, v_k_486_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_486_, v___x_499_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
v___x_502_ = lean_nat_dec_lt(v___x_498_, v___x_487_);
if (v___x_502_ == 0)
{
lean_dec(v___x_498_);
lean_dec_ref(v___x_484_);
return v_as_485_;
}
else
{
lean_object* v___x_503_; lean_object* v_xs_x27_504_; lean_object* v___x_505_; 
v___x_503_ = lean_box(0);
v_xs_x27_504_ = lean_array_fset(v_as_485_, v___x_498_, v___x_503_);
v___x_505_ = lean_array_fset(v_xs_x27_504_, v___x_498_, v___x_484_);
lean_dec(v___x_498_);
return v___x_505_;
}
}
else
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v___x_484_, v_as_485_, v_k_486_, v___x_488_, v___x_498_);
return v___x_506_;
}
}
else
{
lean_object* v___x_507_; 
lean_dec(v___x_498_);
v___x_507_ = lean_array_push(v_as_485_, v___x_484_);
return v___x_507_;
}
}
}
else
{
lean_object* v_as_508_; lean_object* v___x_509_; 
v_as_508_ = lean_array_push(v_as_485_, v___x_484_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_488_, v_as_508_, v___x_487_);
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_array_push(v_as_485_, v___x_484_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object* v___x_511_, lean_object* v_as_512_, lean_object* v_k_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v___x_511_, v_as_512_, v_k_513_);
lean_dec_ref(v_k_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object* v_vs_515_, lean_object* v_v_516_, lean_object* v_i_517_){
_start:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_get_size(v_vs_515_);
v___x_519_ = lean_nat_dec_lt(v_i_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec(v_i_517_);
v___x_520_ = lean_array_push(v_vs_515_, v_v_516_);
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; lean_object* v_val_523_; uint8_t v___x_524_; 
v_val_521_ = lean_ctor_get(v_v_516_, 1);
v___x_522_ = lean_array_fget_borrowed(v_vs_515_, v_i_517_);
v_val_523_ = lean_ctor_get(v___x_522_, 1);
v___x_524_ = lean_expr_eqv(v_val_521_, v_val_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_i_517_, v___x_525_);
lean_dec(v_i_517_);
v_i_517_ = v___x_526_;
goto _start;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_array_fset(v_vs_515_, v_i_517_, v_v_516_);
lean_dec(v_i_517_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object* v_vs_529_, lean_object* v_v_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(v_vs_529_, v_v_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0(lean_object* v_x_533_, lean_object* v_keys_534_, lean_object* v_v_535_, lean_object* v_k_536_, lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_c_540_; lean_object* v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_x_533_, v___x_538_);
v_c_540_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_534_, v_v_535_, v___x_539_);
lean_dec(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_k_536_);
lean_ctor_set(v___x_541_, 1, v_c_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0___boxed(lean_object* v_x_542_, lean_object* v_keys_543_, lean_object* v_v_544_, lean_object* v_k_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_542_, v_keys_543_, v_v_544_, v_k_545_, v_x_546_);
lean_dec_ref(v_keys_543_);
lean_dec(v_x_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_x_552_, lean_object* v_keys_553_, lean_object* v_v_554_, lean_object* v_k_555_, lean_object* v_as_556_, lean_object* v_k_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_mid_562_; lean_object* v_midVal_563_; uint8_t v___x_564_; 
v___x_560_ = lean_nat_add(v_x_558_, v_x_559_);
v___x_561_ = lean_unsigned_to_nat(1u);
v_mid_562_ = lean_nat_shiftr(v___x_560_, v___x_561_);
lean_dec(v___x_560_);
v_midVal_563_ = lean_array_fget(v_as_556_, v_mid_562_);
v___x_564_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_midVal_563_, v_k_557_);
if (v___x_564_ == 0)
{
uint8_t v___x_565_; 
lean_dec(v_x_559_);
v___x_565_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_557_, v_midVal_563_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec(v_x_558_);
v___x_566_ = lean_array_get_size(v_as_556_);
v___x_567_ = lean_nat_dec_lt(v_mid_562_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_midVal_563_);
lean_dec(v_mid_562_);
lean_dec(v_k_555_);
lean_dec_ref(v_v_554_);
return v_as_556_;
}
else
{
lean_object* v_snd_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
v_snd_568_ = lean_ctor_get(v_midVal_563_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_midVal_563_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_midVal_563_, 0);
lean_dec(v_unused_581_);
v___x_570_ = v_midVal_563_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snd_568_);
lean_dec(v_midVal_563_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v_xs_x27_573_; lean_object* v___x_574_; lean_object* v_c_575_; lean_object* v___x_577_; 
v___x_572_ = lean_box(0);
v_xs_x27_573_ = lean_array_fset(v_as_556_, v_mid_562_, v___x_572_);
v___x_574_ = lean_nat_add(v_x_552_, v___x_561_);
v_c_575_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_553_, v_v_554_, v___x_574_, v_snd_568_);
lean_dec(v___x_574_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_c_575_);
lean_ctor_set(v___x_570_, 0, v_k_555_);
v___x_577_ = v___x_570_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_k_555_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_c_575_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = lean_array_fset(v_xs_x27_573_, v_mid_562_, v___x_577_);
lean_dec(v_mid_562_);
return v___x_578_;
}
}
}
}
else
{
lean_dec(v_midVal_563_);
v_x_559_ = v_mid_562_;
goto _start;
}
}
else
{
uint8_t v___x_583_; 
lean_dec(v_midVal_563_);
v___x_583_ = lean_nat_dec_eq(v_mid_562_, v_x_558_);
if (v___x_583_ == 0)
{
lean_dec(v_x_558_);
v_x_558_ = v_mid_562_;
goto _start;
}
else
{
lean_object* v___x_585_; lean_object* v_c_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_j_589_; lean_object* v_as_590_; lean_object* v___x_591_; 
lean_dec(v_mid_562_);
lean_dec(v_x_559_);
v___x_585_ = lean_nat_add(v_x_552_, v___x_561_);
v_c_586_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_553_, v_v_554_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_k_555_);
lean_ctor_set(v___x_587_, 1, v_c_586_);
v___x_588_ = lean_nat_add(v_x_558_, v___x_561_);
lean_dec(v_x_558_);
v_j_589_ = lean_array_get_size(v_as_556_);
v_as_590_ = lean_array_push(v_as_556_, v___x_587_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_588_, v_as_590_, v_j_589_);
lean_dec(v___x_588_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3(lean_object* v_x_592_, lean_object* v_keys_593_, lean_object* v_v_594_, lean_object* v_k_595_, lean_object* v_as_596_, lean_object* v_k_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_array_get_size(v_as_596_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_nat_dec_eq(v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_array_fget_borrowed(v_as_596_, v___x_599_);
v___x_602_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_597_, v___x_601_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; 
v___x_603_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_601_, v_k_597_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_lt(v___x_599_, v___x_598_);
if (v___x_604_ == 0)
{
lean_dec(v_k_595_);
lean_dec_ref(v_v_594_);
return v_as_596_;
}
else
{
lean_object* v___x_605_; lean_object* v_xs_x27_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_inc(v___x_601_);
v___x_605_ = lean_box(0);
v_xs_x27_606_ = lean_array_fset(v_as_596_, v___x_599_, v___x_605_);
v___x_607_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2(v_x_592_, v_keys_593_, v_v_594_, v_k_595_, v___x_601_);
v___x_608_ = lean_array_fset(v_xs_x27_606_, v___x_599_, v___x_607_);
return v___x_608_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_sub(v___x_598_, v___x_609_);
v___x_611_ = lean_array_fget_borrowed(v_as_596_, v___x_610_);
v___x_612_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_611_, v_k_597_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; 
v___x_613_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_597_, v___x_611_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_lt(v___x_610_, v___x_598_);
if (v___x_614_ == 0)
{
lean_dec(v___x_610_);
lean_dec(v_k_595_);
lean_dec_ref(v_v_594_);
return v_as_596_;
}
else
{
lean_object* v___x_615_; lean_object* v_xs_x27_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc(v___x_611_);
v___x_615_ = lean_box(0);
v_xs_x27_616_ = lean_array_fset(v_as_596_, v___x_610_, v___x_615_);
v___x_617_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2(v_x_592_, v_keys_593_, v_v_594_, v_k_595_, v___x_611_);
v___x_618_ = lean_array_fset(v_xs_x27_616_, v___x_610_, v___x_617_);
lean_dec(v___x_610_);
return v___x_618_;
}
}
else
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg(v_x_592_, v_keys_593_, v_v_594_, v_k_595_, v_as_596_, v_k_597_, v___x_599_, v___x_610_);
return v___x_619_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v___x_610_);
v___x_620_ = lean_box(0);
v___x_621_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_592_, v_keys_593_, v_v_594_, v_k_595_, v___x_620_);
v___x_622_ = lean_array_push(v_as_596_, v___x_621_);
return v___x_622_;
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_as_625_; lean_object* v___x_626_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_592_, v_keys_593_, v_v_594_, v_k_595_, v___x_623_);
v_as_625_ = lean_array_push(v_as_596_, v___x_624_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_599_, v_as_625_, v___x_598_);
return v___x_626_;
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_box(0);
v___x_628_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_592_, v_keys_593_, v_v_594_, v_k_595_, v___x_627_);
v___x_629_ = lean_array_push(v_as_596_, v___x_628_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_keys_630_, lean_object* v_v_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v_key_634_; lean_object* v_child_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_669_; 
v_key_634_ = lean_ctor_get(v_x_633_, 0);
v_child_635_ = lean_ctor_get(v_x_633_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_669_ == 0)
{
v___x_637_ = v_x_633_;
v_isShared_638_ = v_isSharedCheck_669_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_child_635_);
lean_inc(v_key_634_);
lean_dec(v_x_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_669_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_array_get_size(v_keys_630_);
v___x_640_ = lean_nat_dec_lt(v_x_632_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_mk_empty_array_with_capacity(v___x_641_);
lean_inc_ref(v___x_642_);
v___x_643_ = lean_array_push(v___x_642_, v_v_631_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_key_634_);
lean_ctor_set(v___x_644_, 1, v_child_635_);
v___x_645_ = lean_array_push(v___x_642_, v___x_644_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 1);
lean_ctor_set(v___x_637_, 1, v___x_645_);
lean_ctor_set(v___x_637_, 0, v___x_643_);
v___x_647_ = v___x_637_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_array_fget_borrowed(v_keys_630_, v_x_632_);
v___x_650_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_649_, v_key_634_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0));
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_key_634_);
lean_ctor_set(v___x_652_, 1, v_child_635_);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_array_push(v___x_654_, v___x_652_);
v___x_656_ = lean_nat_add(v_x_632_, v___x_653_);
v___x_657_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_630_, v_v_631_, v___x_656_);
lean_dec(v___x_656_);
lean_inc(v___x_649_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_649_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
lean_inc_ref(v___x_658_);
v___x_659_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v___x_658_, v___x_655_, v___x_658_);
lean_dec_ref_known(v___x_658_, 2);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 1);
lean_ctor_set(v___x_637_, 1, v___x_659_);
lean_ctor_set(v___x_637_, 0, v___x_651_);
v___x_661_ = v___x_637_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_x_632_, v___x_663_);
v___x_665_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_630_, v_v_631_, v___x_664_, v_child_635_);
lean_dec(v___x_664_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_665_);
v___x_667_ = v___x_637_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_key_634_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
else
{
lean_object* v_vs_670_; lean_object* v_children_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_688_; 
v_vs_670_ = lean_ctor_get(v_x_633_, 0);
v_children_671_ = lean_ctor_get(v_x_633_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_688_ == 0)
{
v___x_673_ = v_x_633_;
v_isShared_674_ = v_isSharedCheck_688_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_children_671_);
lean_inc(v_vs_670_);
lean_dec(v_x_633_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_688_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_keys_630_);
v___x_676_ = lean_nat_dec_lt(v_x_632_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_vs_670_, v_v_631_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_677_);
v___x_679_ = v___x_673_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_children_671_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v_k_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_c_684_; lean_object* v___x_686_; 
v_k_681_ = lean_array_fget_borrowed(v_keys_630_, v_x_632_);
v___x_682_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_681_, 2);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_k_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v_c_684_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3(v_x_632_, v_keys_630_, v_v_631_, v_k_681_, v_children_671_, v___x_683_);
lean_dec_ref_known(v___x_683_, 2);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_c_684_);
v___x_686_ = v___x_673_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_vs_670_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_c_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2(lean_object* v_x_689_, lean_object* v_keys_690_, lean_object* v_v_691_, lean_object* v_k_692_, lean_object* v_x_693_){
_start:
{
lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_704_; 
v_snd_694_ = lean_ctor_get(v_x_693_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_693_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_x_693_, 0);
lean_dec(v_unused_705_);
v___x_696_ = v_x_693_;
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_dec(v_x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_c_700_; lean_object* v___x_702_; 
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_x_689_, v___x_698_);
v_c_700_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_690_, v_v_691_, v___x_699_, v_snd_694_);
lean_dec(v___x_699_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_c_700_);
lean_ctor_set(v___x_696_, 0, v_k_692_);
v___x_702_ = v___x_696_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_k_692_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_c_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2___boxed(lean_object* v_x_706_, lean_object* v_keys_707_, lean_object* v_v_708_, lean_object* v_k_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___lam__2(v_x_706_, v_keys_707_, v_v_708_, v_k_709_, v_x_710_);
lean_dec_ref(v_keys_707_);
lean_dec(v_x_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg___boxed(lean_object* v_x_712_, lean_object* v_keys_713_, lean_object* v_v_714_, lean_object* v_k_715_, lean_object* v_as_716_, lean_object* v_k_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg(v_x_712_, v_keys_713_, v_v_714_, v_k_715_, v_as_716_, v_k_717_, v_x_718_, v_x_719_);
lean_dec_ref(v_k_717_);
lean_dec_ref(v_keys_713_);
lean_dec(v_x_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_721_, lean_object* v_v_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_721_, v_v_722_, v_x_723_, v_x_724_);
lean_dec(v_x_723_);
lean_dec_ref(v_keys_721_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3___boxed(lean_object* v_x_726_, lean_object* v_keys_727_, lean_object* v_v_728_, lean_object* v_k_729_, lean_object* v_as_730_, lean_object* v_k_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3(v_x_726_, v_keys_727_, v_v_728_, v_k_729_, v_as_730_, v_k_731_);
lean_dec_ref(v_k_731_);
lean_dec_ref(v_keys_727_);
lean_dec(v_x_726_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_733_, lean_object* v_v_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_733_, v_v_734_, v___x_736_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
else
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v_val_739_ = lean_ctor_get(v_x_735_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_741_ = v_x_735_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v_x_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_733_, v_v_734_, v___x_743_, v_val_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_744_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_749_, lean_object* v_v_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_749_, v_v_750_, v_x_751_);
lean_dec_ref(v_keys_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_keys_753_, lean_object* v_v_754_, lean_object* v_x_755_, size_t v_x_756_, size_t v_x_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
lean_object* v_es_759_; size_t v___x_760_; size_t v___x_761_; lean_object* v_j_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_es_759_ = lean_ctor_get(v_x_755_, 0);
v___x_760_ = ((size_t)31ULL);
v___x_761_ = lean_usize_land(v_x_756_, v___x_760_);
v_j_762_ = lean_usize_to_nat(v___x_761_);
v___x_763_ = lean_array_get_size(v_es_759_);
v___x_764_ = lean_nat_dec_lt(v_j_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_dec(v_j_762_);
lean_dec(v_x_758_);
lean_dec_ref(v_v_754_);
return v_x_755_;
}
else
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_832_; 
lean_inc_ref(v_es_759_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_755_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_x_755_, 0);
lean_dec(v_unused_833_);
v___x_766_ = v_x_755_;
v_isShared_767_ = v_isSharedCheck_832_;
goto v_resetjp_765_;
}
else
{
lean_dec(v_x_755_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_832_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_v_768_; lean_object* v___x_769_; lean_object* v_xs_x27_770_; lean_object* v___y_772_; 
v_v_768_ = lean_array_fget(v_es_759_, v_j_762_);
v___x_769_ = lean_box(0);
v_xs_x27_770_ = lean_array_fset(v_es_759_, v_j_762_, v___x_769_);
switch(lean_obj_tag(v_v_768_))
{
case 0:
{
lean_object* v_key_777_; lean_object* v_val_778_; uint8_t v___x_779_; 
v_key_777_ = lean_ctor_get(v_v_768_, 0);
v_val_778_ = lean_ctor_get(v_v_768_, 1);
v___x_779_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_758_, v_key_777_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_753_, v_v_754_, v___x_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_dec(v_x_758_);
v___y_772_ = v_v_768_;
goto v___jp_771_;
}
else
{
lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
lean_inc(v_val_778_);
lean_inc(v_key_777_);
lean_dec_ref_known(v_v_768_, 2);
v_val_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_777_, v_val_778_, v_x_758_, v_val_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
v___y_772_ = v___x_788_;
goto v___jp_771_;
}
}
}
}
else
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_801_; 
lean_inc(v_val_778_);
v_isSharedCheck_801_ = !lean_is_exclusive(v_v_768_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_802_ = lean_ctor_get(v_v_768_, 1);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_v_768_, 0);
lean_dec(v_unused_803_);
v___x_792_ = v_v_768_;
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_v_768_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v_val_778_);
v___x_795_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_753_, v_v_754_, v___x_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
lean_del_object(v___x_792_);
lean_dec(v_x_758_);
v___x_796_ = lean_box(2);
v___y_772_ = v___x_796_;
goto v___jp_771_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; 
v_val_797_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_795_, 1);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v_val_797_);
lean_ctor_set(v___x_792_, 0, v_x_758_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_x_758_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_val_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v___y_772_ = v___x_799_;
goto v___jp_771_;
}
}
}
}
}
case 1:
{
lean_object* v_node_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_827_; 
v_node_804_ = lean_ctor_get(v_v_768_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_v_768_);
if (v_isSharedCheck_827_ == 0)
{
v___x_806_ = v_v_768_;
v_isShared_807_ = v_isSharedCheck_827_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_node_804_);
lean_dec(v_v_768_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_827_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v_newNode_812_; lean_object* v___x_813_; 
v___x_808_ = ((size_t)5ULL);
v___x_809_ = lean_usize_shift_right(v_x_756_, v___x_808_);
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_x_757_, v___x_810_);
v_newNode_812_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_753_, v_v_754_, v_node_804_, v___x_809_, v___x_811_, v_x_758_);
lean_inc_ref(v_newNode_812_);
v___x_813_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_815_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v_newNode_812_);
v___x_815_ = v___x_806_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_newNode_812_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v___y_772_ = v___x_815_;
goto v___jp_771_;
}
}
else
{
lean_object* v_val_817_; lean_object* v_fst_818_; lean_object* v_snd_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_newNode_812_);
lean_del_object(v___x_806_);
v_val_817_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_813_, 1);
v_fst_818_ = lean_ctor_get(v_val_817_, 0);
v_snd_819_ = lean_ctor_get(v_val_817_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_val_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v_val_817_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_snd_819_);
lean_inc(v_fst_818_);
lean_dec(v_val_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_fst_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_snd_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v___y_772_ = v___x_824_;
goto v___jp_771_;
}
}
}
}
}
default: 
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_box(0);
v___x_829_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_753_, v_v_754_, v___x_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec(v_x_758_);
v___y_772_ = v_v_768_;
goto v___jp_771_;
}
else
{
lean_object* v_val_830_; lean_object* v___x_831_; 
v_val_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_x_758_);
lean_ctor_set(v___x_831_, 1, v_val_830_);
v___y_772_ = v___x_831_;
goto v___jp_771_;
}
}
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_array_fset(v_xs_x27_770_, v_j_762_, v___y_772_);
lean_dec(v_j_762_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_773_);
v___x_775_ = v___x_766_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_868_; 
v_ks_834_ = lean_ctor_get(v_x_755_, 0);
v_vs_835_ = lean_ctor_get(v_x_755_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_755_);
if (v_isSharedCheck_868_ == 0)
{
v___x_837_ = v_x_755_;
v_isShared_838_ = v_isSharedCheck_868_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_vs_835_);
lean_inc(v_ks_834_);
lean_dec(v_x_755_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_868_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(v_ks_834_, v_x_758_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_841_; 
if (v_isShared_838_ == 0)
{
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_ks_834_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_vs_835_);
v___x_841_ = v_reuseFailAlloc_846_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_box(0);
v___x_843_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_753_, v_v_754_, v___x_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_dec(v_x_758_);
return v___x_841_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_845_; 
v_val_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(v___x_841_, v_x_756_, v_x_757_, v_x_758_, v_val_844_);
return v___x_845_;
}
}
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_867_; 
v_val_847_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_867_ == 0)
{
v___x_849_ = v___x_839_;
v_isShared_850_ = v_isSharedCheck_867_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v___x_839_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_867_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_v_x27_851_; lean_object* v_keys_852_; lean_object* v_vals_853_; lean_object* v___x_855_; 
v_v_x27_851_ = lean_array_fget(v_vs_835_, v_val_847_);
lean_inc(v_val_847_);
v_keys_852_ = l_Array_eraseIdx___redArg(v_ks_834_, v_val_847_);
v_vals_853_ = l_Array_eraseIdx___redArg(v_vs_835_, v_val_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_v_x27_851_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_v_x27_851_);
v___x_855_ = v_reuseFailAlloc_866_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_753_, v_v_754_, v___x_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_858_; 
lean_dec(v_x_758_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_vals_853_);
lean_ctor_set(v___x_837_, 0, v_keys_852_);
v___x_858_ = v___x_837_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_keys_852_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_vals_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
lean_object* v_val_860_; lean_object* v_keys_861_; lean_object* v_vals_862_; lean_object* v___x_864_; 
v_val_860_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v___x_856_, 1);
v_keys_861_ = lean_array_push(v_keys_852_, v_x_758_);
v_vals_862_ = lean_array_push(v_vals_853_, v_val_860_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_vals_862_);
lean_ctor_set(v___x_837_, 0, v_keys_861_);
v___x_864_ = v___x_837_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_keys_861_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_vals_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_869_, lean_object* v_v_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
size_t v_x_3951__boxed_875_; size_t v_x_3952__boxed_876_; lean_object* v_res_877_; 
v_x_3951__boxed_875_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_3952__boxed_876_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_877_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_869_, v_v_870_, v_x_871_, v_x_3951__boxed_875_, v_x_3952__boxed_876_, v_x_874_);
lean_dec_ref(v_keys_869_);
return v_res_877_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_882_ = lean_unsigned_to_nat(23u);
v___x_883_ = lean_unsigned_to_nat(177u);
v___x_884_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_885_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_886_ = l_mkPanicMessageWithDecl(v___x_885_, v___x_884_, v___x_883_, v___x_882_, v___x_881_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_887_, lean_object* v_keys_888_, lean_object* v_v_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = lean_array_get_size(v_keys_888_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_nat_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v_k_894_; uint64_t v___x_895_; size_t v_h_896_; size_t v___x_897_; lean_object* v___x_898_; 
v___x_893_ = lean_box(0);
v_k_894_ = lean_array_get_borrowed(v___x_893_, v_keys_888_, v___x_891_);
v___x_895_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_894_);
v_h_896_ = lean_uint64_to_usize(v___x_895_);
v___x_897_ = ((size_t)1ULL);
lean_inc(v_k_894_);
v___x_898_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_888_, v_v_889_, v_d_887_, v_h_896_, v___x_897_, v_k_894_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec_ref(v_v_889_);
lean_dec_ref(v_d_887_);
v___x_899_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_900_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_901_, lean_object* v_keys_902_, lean_object* v_v_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_901_, v_keys_902_, v_v_903_);
lean_dec_ref(v_keys_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14_spec__22(lean_object* v_xs_905_, lean_object* v_v_906_, lean_object* v_i_907_){
_start:
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_array_get_size(v_xs_905_);
v___x_909_ = lean_nat_dec_lt(v_i_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v_i_907_);
v___x_910_ = lean_box(0);
return v___x_910_;
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_array_fget_borrowed(v_xs_905_, v_i_907_);
v___x_912_ = lean_name_eq(v___x_911_, v_v_906_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_add(v_i_907_, v___x_913_);
lean_dec(v_i_907_);
v_i_907_ = v___x_914_;
goto _start;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_i_907_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14_spec__22___boxed(lean_object* v_xs_917_, lean_object* v_v_918_, lean_object* v_i_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14_spec__22(v_xs_917_, v_v_918_, v_i_919_);
lean_dec(v_v_918_);
lean_dec_ref(v_xs_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14(lean_object* v_xs_921_, lean_object* v_v_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14_spec__22(v_xs_921_, v_v_922_, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14___boxed(lean_object* v_xs_925_, lean_object* v_v_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14(v_xs_925_, v_v_926_);
lean_dec(v_v_926_);
lean_dec_ref(v_xs_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(lean_object* v_x_928_, size_t v_x_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
lean_object* v_es_931_; lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v_j_935_; lean_object* v_entry_936_; 
v_es_931_ = lean_ctor_get(v_x_928_, 0);
v___x_932_ = lean_box(2);
v___x_933_ = ((size_t)31ULL);
v___x_934_ = lean_usize_land(v_x_929_, v___x_933_);
v_j_935_ = lean_usize_to_nat(v___x_934_);
v_entry_936_ = lean_array_get(v___x_932_, v_es_931_, v_j_935_);
switch(lean_obj_tag(v_entry_936_))
{
case 0:
{
lean_object* v_key_937_; uint8_t v___x_938_; 
v_key_937_ = lean_ctor_get(v_entry_936_, 0);
lean_inc(v_key_937_);
lean_dec_ref_known(v_entry_936_, 2);
v___x_938_ = lean_name_eq(v_x_930_, v_key_937_);
lean_dec(v_key_937_);
if (v___x_938_ == 0)
{
lean_dec(v_j_935_);
return v_x_928_;
}
else
{
lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
lean_inc_ref(v_es_931_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_x_928_, 0);
lean_dec(v_unused_947_);
v___x_940_ = v_x_928_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_dec(v_x_928_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_array_set(v_es_931_, v_j_935_, v___x_932_);
lean_dec(v_j_935_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
case 1:
{
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_982_; 
lean_inc_ref(v_es_931_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_x_928_, 0);
lean_dec(v_unused_983_);
v___x_949_ = v_x_928_;
v_isShared_950_ = v_isSharedCheck_982_;
goto v_resetjp_948_;
}
else
{
lean_dec(v_x_928_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_982_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_node_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_981_; 
v_node_951_ = lean_ctor_get(v_entry_936_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_entry_936_);
if (v_isSharedCheck_981_ == 0)
{
v___x_953_ = v_entry_936_;
v_isShared_954_ = v_isSharedCheck_981_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_node_951_);
lean_dec(v_entry_936_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_981_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
size_t v___x_955_; lean_object* v_entries_956_; size_t v___x_957_; lean_object* v_newNode_958_; lean_object* v___x_959_; 
v___x_955_ = ((size_t)5ULL);
v_entries_956_ = lean_array_set(v_es_931_, v_j_935_, v___x_932_);
v___x_957_ = lean_usize_shift_right(v_x_929_, v___x_955_);
v_newNode_958_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_node_951_, v___x_957_, v_x_930_);
lean_inc_ref(v_newNode_958_);
v___x_959_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_961_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_newNode_958_);
v___x_961_ = v___x_953_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_newNode_958_);
v___x_961_ = v_reuseFailAlloc_966_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_array_set(v_entries_956_, v_j_935_, v___x_961_);
lean_dec(v_j_935_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_962_);
v___x_964_ = v___x_949_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_val_967_; lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_newNode_958_);
lean_del_object(v___x_953_);
v_val_967_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v___x_959_, 1);
v_fst_968_ = lean_ctor_get(v_val_967_, 0);
v_snd_969_ = lean_ctor_get(v_val_967_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_val_967_);
if (v_isSharedCheck_980_ == 0)
{
v___x_971_ = v_val_967_;
v_isShared_972_ = v_isSharedCheck_980_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_snd_969_);
lean_inc(v_fst_968_);
lean_dec(v_val_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_980_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_fst_968_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_snd_969_);
v___x_974_ = v_reuseFailAlloc_979_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_array_set(v_entries_956_, v_j_935_, v___x_974_);
lean_dec(v_j_935_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_975_);
v___x_977_ = v___x_949_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_935_);
return v_x_928_;
}
}
}
else
{
lean_object* v_ks_984_; lean_object* v_vs_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_999_; 
v_ks_984_ = lean_ctor_get(v_x_928_, 0);
v_vs_985_ = lean_ctor_get(v_x_928_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_999_ == 0)
{
v___x_987_ = v_x_928_;
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_vs_985_);
lean_inc(v_ks_984_);
lean_dec(v_x_928_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; 
v___x_989_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__14(v_ks_984_, v_x_930_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_991_; 
if (v_isShared_988_ == 0)
{
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_ks_984_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_vs_985_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v_val_993_; lean_object* v_keys_x27_994_; lean_object* v_vals_x27_995_; lean_object* v___x_997_; 
v_val_993_ = lean_ctor_get(v___x_989_, 0);
lean_inc_n(v_val_993_, 2);
lean_dec_ref_known(v___x_989_, 1);
v_keys_x27_994_ = l_Array_eraseIdx___redArg(v_ks_984_, v_val_993_);
v_vals_x27_995_ = l_Array_eraseIdx___redArg(v_vs_985_, v_val_993_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_vals_x27_995_);
lean_ctor_set(v___x_987_, 0, v_keys_x27_994_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_keys_x27_994_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_vals_x27_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg___boxed(lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
size_t v_x_4232__boxed_1003_; lean_object* v_res_1004_; 
v_x_4232__boxed_1003_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_res_1004_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_1000_, v_x_4232__boxed_1003_, v_x_1002_);
lean_dec(v_x_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
uint64_t v___y_1008_; 
if (lean_obj_tag(v_x_1006_) == 0)
{
uint64_t v___x_1011_; 
v___x_1011_ = 1723ULL;
v___y_1008_ = v___x_1011_;
goto v___jp_1007_;
}
else
{
uint64_t v_hash_1012_; 
v_hash_1012_ = lean_ctor_get_uint64(v_x_1006_, sizeof(void*)*2);
v___y_1008_ = v_hash_1012_;
goto v___jp_1007_;
}
v___jp_1007_:
{
size_t v_h_1009_; lean_object* v___x_1010_; 
v_h_1009_ = lean_uint64_to_usize(v___y_1008_);
v___x_1010_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_1005_, v_h_1009_, v_x_1006_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_1013_, v_x_1014_);
lean_dec(v_x_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_1016_, lean_object* v_e_1017_){
_start:
{
lean_object* v_globalName_x3f_1018_; 
v_globalName_x3f_1018_ = lean_ctor_get(v_e_1017_, 3);
if (lean_obj_tag(v_globalName_x3f_1018_) == 0)
{
lean_object* v_keys_1019_; lean_object* v_discrTree_1020_; lean_object* v_instanceNames_1021_; lean_object* v_erased_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_keys_1019_ = lean_ctor_get(v_e_1017_, 0);
lean_inc_ref(v_keys_1019_);
v_discrTree_1020_ = lean_ctor_get(v_d_1016_, 0);
v_instanceNames_1021_ = lean_ctor_get(v_d_1016_, 1);
v_erased_1022_ = lean_ctor_get(v_d_1016_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_d_1016_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_d_1016_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_erased_1022_);
lean_inc(v_instanceNames_1021_);
lean_inc(v_discrTree_1020_);
lean_dec(v_d_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_1020_, v_keys_1019_, v_e_1017_);
lean_dec_ref(v_keys_1019_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_instanceNames_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_erased_1022_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_keys_1031_; lean_object* v_val_1032_; lean_object* v_discrTree_1033_; lean_object* v_instanceNames_1034_; lean_object* v_erased_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_keys_1031_ = lean_ctor_get(v_e_1017_, 0);
v_val_1032_ = lean_ctor_get(v_globalName_x3f_1018_, 0);
lean_inc(v_val_1032_);
v_discrTree_1033_ = lean_ctor_get(v_d_1016_, 0);
v_instanceNames_1034_ = lean_ctor_get(v_d_1016_, 1);
v_erased_1035_ = lean_ctor_get(v_d_1016_, 2);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_d_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1037_ = v_d_1016_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_erased_1035_);
lean_inc(v_instanceNames_1034_);
lean_inc(v_discrTree_1033_);
lean_dec(v_d_1016_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_inc_ref(v_e_1017_);
v___x_1039_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_1033_, v_keys_1031_, v_e_1017_);
lean_inc(v_val_1032_);
v___x_1040_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_1034_, v_val_1032_, v_e_1017_);
v___x_1041_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_1035_, v_val_1032_);
lean_dec(v_val_1032_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 2, v___x_1041_);
lean_ctor_set(v___x_1037_, 1, v___x_1040_);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_1047_, v_x_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_1052_, v_x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_1055_, v_x_1056_, v_x_1057_);
lean_dec(v_x_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, size_t v_x_1061_, size_t v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_1060_, v_x_1061_, v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
size_t v_x_4436__boxed_1072_; size_t v_x_4437__boxed_1073_; lean_object* v_res_1074_; 
v_x_4436__boxed_1072_ = lean_unbox_usize(v_x_1068_);
lean_dec(v_x_1068_);
v_x_4437__boxed_1073_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_res_1074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(v_00_u03b2_1066_, v_x_1067_, v_x_4436__boxed_1072_, v_x_4437__boxed_1073_, v_x_1070_, v_x_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, size_t v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
size_t v_x_4453__boxed_1084_; lean_object* v_res_1085_; 
v_x_4453__boxed_1084_ = lean_unbox_usize(v_x_1082_);
lean_dec(v_x_1082_);
v_res_1085_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(v_00_u03b2_1080_, v_x_1081_, v_x_4453__boxed_1084_, v_x_1083_);
lean_dec(v_x_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, size_t v_x_1088_, size_t v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___redArg(v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_4464__boxed_1099_; size_t v_x_4465__boxed_1100_; lean_object* v_res_1101_; 
v_x_4464__boxed_1099_ = lean_unbox_usize(v_x_1095_);
lean_dec(v_x_1095_);
v_x_4465__boxed_1100_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_res_1101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6(v_00_u03b2_1093_, v_x_1094_, v_x_4464__boxed_1099_, v_x_4465__boxed_1100_, v_x_1097_, v_x_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1102_, lean_object* v_n_1103_, lean_object* v_k_1104_, lean_object* v_v_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_n_1103_, v_k_1104_, v_v_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_1107_, size_t v_depth_1108_, lean_object* v_keys_1109_, lean_object* v_vals_1110_, lean_object* v_heq_1111_, lean_object* v_i_1112_, lean_object* v_entries_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___redArg(v_depth_1108_, v_keys_1109_, v_vals_1110_, v_i_1112_, v_entries_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_1115_, lean_object* v_depth_1116_, lean_object* v_keys_1117_, lean_object* v_vals_1118_, lean_object* v_heq_1119_, lean_object* v_i_1120_, lean_object* v_entries_1121_){
_start:
{
size_t v_depth_boxed_1122_; lean_object* v_res_1123_; 
v_depth_boxed_1122_ = lean_unbox_usize(v_depth_1116_);
lean_dec(v_depth_1116_);
v_res_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__11(v_00_u03b2_1115_, v_depth_boxed_1122_, v_keys_1117_, v_vals_1118_, v_heq_1119_, v_i_1120_, v_entries_1121_);
lean_dec_ref(v_vals_1118_);
lean_dec_ref(v_keys_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_1124_, lean_object* v_as_1125_, lean_object* v_k_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___redArg(v___x_1124_, v_as_1125_, v_k_1126_, v_x_1127_, v_x_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_1132_, lean_object* v_as_1133_, lean_object* v_k_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v___x_1132_, v_as_1133_, v_k_1134_, v_x_1135_, v_x_1136_, v_x_1137_, v_x_1138_);
lean_dec_ref(v_k_1134_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9(lean_object* v_x_1140_, lean_object* v_keys_1141_, lean_object* v_v_1142_, lean_object* v_k_1143_, lean_object* v_as_1144_, lean_object* v_k_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___redArg(v_x_1140_, v_keys_1141_, v_v_1142_, v_k_1143_, v_as_1144_, v_k_1145_, v_x_1146_, v_x_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_x_1151_, lean_object* v_keys_1152_, lean_object* v_v_1153_, lean_object* v_k_1154_, lean_object* v_as_1155_, lean_object* v_k_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__3_spec__9(v_x_1151_, v_keys_1152_, v_v_1153_, v_k_1154_, v_as_1155_, v_k_1156_, v_x_1157_, v_x_1158_, v_x_1159_, v_x_1160_);
lean_dec_ref(v_k_1156_);
lean_dec_ref(v_keys_1152_);
lean_dec(v_x_1151_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_1162_, lean_object* v_n_1163_, lean_object* v_k_1164_, lean_object* v_v_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(v_n_1163_, v_k_1164_, v_v_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15(lean_object* v_00_u03b2_1167_, size_t v_depth_1168_, lean_object* v_keys_1169_, lean_object* v_vals_1170_, lean_object* v_heq_1171_, lean_object* v_i_1172_, lean_object* v_entries_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___redArg(v_depth_1168_, v_keys_1169_, v_vals_1170_, v_i_1172_, v_entries_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15___boxed(lean_object* v_00_u03b2_1175_, lean_object* v_depth_1176_, lean_object* v_keys_1177_, lean_object* v_vals_1178_, lean_object* v_heq_1179_, lean_object* v_i_1180_, lean_object* v_entries_1181_){
_start:
{
size_t v_depth_boxed_1182_; lean_object* v_res_1183_; 
v_depth_boxed_1182_ = lean_unbox_usize(v_depth_1176_);
lean_dec(v_depth_1176_);
v_res_1183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__15(v_00_u03b2_1175_, v_depth_boxed_1182_, v_keys_1177_, v_vals_1178_, v_heq_1179_, v_i_1180_, v_entries_1181_);
lean_dec_ref(v_vals_1178_);
lean_dec_ref(v_keys_1177_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10_spec__18(lean_object* v_00_u03b2_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10_spec__18___redArg(v_x_1185_, v_x_1186_, v_x_1187_, v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14_spec__17(lean_object* v_00_u03b2_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__6_spec__14_spec__17___redArg(v_x_1191_, v_x_1192_, v_x_1193_, v_x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1196_, lean_object* v_declName_1197_){
_start:
{
lean_object* v_discrTree_1198_; lean_object* v_instanceNames_1199_; lean_object* v_erased_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_discrTree_1198_ = lean_ctor_get(v_d_1196_, 0);
v_instanceNames_1199_ = lean_ctor_get(v_d_1196_, 1);
v_erased_1200_ = lean_ctor_get(v_d_1196_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_d_1196_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v_d_1196_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_erased_1200_);
lean_inc(v_instanceNames_1199_);
lean_inc(v_discrTree_1198_);
lean_dec(v_d_1196_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1204_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1199_, v_declName_1197_);
v___x_1205_ = lean_box(0);
v___x_1206_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1200_, v_declName_1197_, v___x_1205_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 2, v___x_1206_);
lean_ctor_set(v___x_1202_, 1, v___x_1204_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_discrTree_1198_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1211_, lean_object* v_declName_1212_, lean_object* v_toPure_1213_, lean_object* v_____r_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = l_Lean_Meta_Instances_eraseCore(v_d_1211_, v_declName_1212_);
v___x_1216_ = lean_apply_2(v_toPure_1213_, lean_box(0), v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1217_, lean_object* v_____r_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_apply_1(v___f_1217_, v_____r_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_d_1230_, lean_object* v_declName_1231_){
_start:
{
lean_object* v_toApplicative_1232_; lean_object* v_toBind_1233_; lean_object* v_toPure_1234_; lean_object* v_instanceNames_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___f_1238_; uint8_t v___x_1239_; 
v_toApplicative_1232_ = lean_ctor_get(v_inst_1228_, 0);
v_toBind_1233_ = lean_ctor_get(v_inst_1228_, 1);
lean_inc(v_toBind_1233_);
v_toPure_1234_ = lean_ctor_get(v_toApplicative_1232_, 1);
v_instanceNames_1235_ = lean_ctor_get(v_d_1230_, 1);
v___x_1236_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1237_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1234_);
lean_inc_n(v_declName_1231_, 2);
lean_inc_ref(v_d_1230_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1238_, 0, v_d_1230_);
lean_closure_set(v___f_1238_, 1, v_declName_1231_);
lean_closure_set(v___f_1238_, 2, v_toPure_1234_);
lean_inc_ref(v_instanceNames_1235_);
v___x_1239_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1236_, v___x_1237_, v_instanceNames_1235_, v_declName_1231_);
if (v___x_1239_ == 0)
{
lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v_d_1230_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1240_, 0, v___f_1238_);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1242_ = l_Lean_MessageData_ofConstName(v_declName_1231_, v___x_1239_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_throwError___redArg(v_inst_1228_, v_inst_1229_, v___x_1245_);
v___x_1247_ = lean_apply_4(v_toBind_1233_, lean_box(0), lean_box(0), v___x_1246_, v___f_1240_);
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_inc(v_toPure_1234_);
lean_dec_ref(v___f_1238_);
lean_dec(v_toBind_1233_);
lean_dec_ref(v_inst_1229_);
lean_dec_ref(v_inst_1228_);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1230_, v_declName_1231_, v_toPure_1234_, v___x_1248_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_d_1253_, lean_object* v_declName_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1251_, v_inst_1252_, v_d_1253_, v_declName_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(lean_object* v_x_1256_, lean_object* v_e_1257_){
_start:
{
lean_object* v_globalName_x3f_1262_; 
v_globalName_x3f_1262_ = lean_ctor_get(v_e_1257_, 3);
lean_inc(v_globalName_x3f_1262_);
if (lean_obj_tag(v_globalName_x3f_1262_) == 0)
{
goto v___jp_1258_;
}
else
{
lean_object* v_val_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1272_; 
v_val_1263_ = lean_ctor_get(v_globalName_x3f_1262_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_globalName_x3f_1262_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1265_ = v_globalName_x3f_1262_;
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_val_1263_);
lean_dec(v_globalName_x3f_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
uint8_t v___x_1267_; 
v___x_1267_ = l_Lean_isPrivateName(v_val_1263_);
lean_dec(v_val_1263_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1269_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_e_1257_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_e_1257_);
v___x_1269_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; 
lean_inc_ref_n(v___x_1269_, 2);
v___x_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
lean_ctor_set(v___x_1270_, 2, v___x_1269_);
return v___x_1270_;
}
}
else
{
lean_del_object(v___x_1265_);
goto v___jp_1258_;
}
}
}
v___jp_1258_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_e_1257_);
v___x_1261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1259_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object* v_x_1273_, lean_object* v_e_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(v_x_1273_, v_e_1274_);
lean_dec_ref(v_x_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(lean_object* v___y_1276_){
_start:
{
lean_inc_ref(v___y_1276_);
return v___y_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(v___y_1277_);
lean_dec_ref(v___y_1277_);
return v_res_1278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; uint8_t v___x_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1287_ = lean_box(0);
v___x_1288_ = 0;
v___x_1289_ = 1;
v___f_1290_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___f_1291_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___x_1292_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___x_1295_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
lean_ctor_set(v___x_1295_, 2, v___x_1292_);
lean_ctor_set(v___x_1295_, 3, v___f_1291_);
lean_ctor_set(v___x_1295_, 4, v___f_1290_);
lean_ctor_set(v___x_1295_, 5, v___x_1287_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*6, v___x_1289_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*6 + 1, v___x_1288_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_);
v___x_1298_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_();
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1301_, uint8_t v_allowLevelAssignments_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1302_, v_k_1301_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1308_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1308_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1325_, lean_object* v_allowLevelAssignments_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1332_; lean_object* v_res_1333_; 
v_allowLevelAssignments_boxed_1332_ = lean_unbox(v_allowLevelAssignments_1326_);
v_res_1333_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1325_, v_allowLevelAssignments_boxed_1332_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1334_, lean_object* v_k_1335_, uint8_t v_allowLevelAssignments_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1335_, v_allowLevelAssignments_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_k_1344_, lean_object* v_allowLevelAssignments_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1351_; lean_object* v_res_1352_; 
v_allowLevelAssignments_boxed_1351_ = lean_unbox(v_allowLevelAssignments_1345_);
v_res_1352_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1343_, v_k_1344_, v_allowLevelAssignments_boxed_1351_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1353_, lean_object* v___x_1354_, uint8_t v___x_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1353_, v___x_1354_, v___x_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v_snd_1363_; lean_object* v_snd_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v_snd_1363_ = lean_ctor_get(v_a_1362_, 1);
lean_inc(v_snd_1363_);
lean_dec(v_a_1362_);
v_snd_1364_ = lean_ctor_get(v_snd_1363_, 1);
lean_inc(v_snd_1364_);
lean_dec(v_snd_1363_);
v___x_1365_ = 0;
v___x_1366_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1364_, v___x_1365_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1366_;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1361_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1361_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1375_, lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v___x_497__boxed_1383_; lean_object* v_res_1384_; 
v___x_497__boxed_1383_ = lean_unbox(v___x_1377_);
v_res_1384_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1375_, v___x_1376_, v___x_497__boxed_1383_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___x_1391_; 
lean_inc(v_a_1389_);
lean_inc_ref(v_a_1388_);
lean_inc(v_a_1387_);
lean_inc_ref(v_a_1386_);
v___x_1391_ = lean_infer_type(v_e_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = lean_box(0);
v___x_1394_ = 0;
v___x_1395_ = lean_box(v___x_1394_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1396_, 0, v_a_1392_);
lean_closure_set(v___f_1396_, 1, v___x_1393_);
lean_closure_set(v___f_1396_, 2, v___x_1395_);
v___x_1397_ = 0;
v___x_1398_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1396_, v___x_1397_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
return v___x_1398_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1391_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1391_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1414_, lean_object* v_b_1415_, lean_object* v_c_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
v___x_1422_ = lean_apply_7(v_k_1414_, v_b_1415_, v_c_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, lean_box(0));
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1423_, lean_object* v_b_1424_, lean_object* v_c_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1423_, v_b_1424_, v_c_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1432_, lean_object* v_k_1433_, uint8_t v_cleanupAnnotations_1434_, uint8_t v_whnfType_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___f_1441_; lean_object* v___x_1442_; 
v___f_1441_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1441_, 0, v_k_1433_);
v___x_1442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1432_, v___f_1441_, v_cleanupAnnotations_1434_, v_whnfType_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1442_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1442_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1459_, lean_object* v_k_1460_, lean_object* v_cleanupAnnotations_1461_, lean_object* v_whnfType_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1468_; uint8_t v_whnfType_boxed_1469_; lean_object* v_res_1470_; 
v_cleanupAnnotations_boxed_1468_ = lean_unbox(v_cleanupAnnotations_1461_);
v_whnfType_boxed_1469_ = lean_unbox(v_whnfType_1462_);
v_res_1470_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1459_, v_k_1460_, v_cleanupAnnotations_boxed_1468_, v_whnfType_boxed_1469_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1471_, lean_object* v_type_1472_, lean_object* v_k_1473_, uint8_t v_cleanupAnnotations_1474_, uint8_t v_whnfType_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1472_, v_k_1473_, v_cleanupAnnotations_1474_, v_whnfType_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_type_1483_, lean_object* v_k_1484_, lean_object* v_cleanupAnnotations_1485_, lean_object* v_whnfType_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1492_; uint8_t v_whnfType_boxed_1493_; lean_object* v_res_1494_; 
v_cleanupAnnotations_boxed_1492_ = lean_unbox(v_cleanupAnnotations_1485_);
v_whnfType_boxed_1493_ = lean_unbox(v_whnfType_1486_);
v_res_1494_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1482_, v_type_1483_, v_k_1484_, v_cleanupAnnotations_boxed_1492_, v_whnfType_boxed_1493_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1498_, size_t v_sz_1499_, size_t v_i_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_a_1508_; uint8_t v___x_1512_; 
v___x_1512_ = lean_usize_dec_lt(v_i_1500_, v_sz_1499_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_b_1501_);
return v___x_1513_;
}
else
{
lean_object* v_fst_1514_; lean_object* v_snd_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1562_; 
v_fst_1514_ = lean_ctor_get(v_b_1501_, 0);
v_snd_1515_ = lean_ctor_get(v_b_1501_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_b_1501_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1517_ = v_b_1501_;
v_isShared_1518_ = v_isSharedCheck_1562_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_snd_1515_);
lean_inc(v_fst_1514_);
lean_dec(v_b_1501_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1562_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_next_1524_; 
v_next_1524_ = lean_ctor_get(v_snd_1515_, 0);
lean_inc(v_next_1524_);
if (lean_obj_tag(v_next_1524_) == 0)
{
goto v___jp_1519_;
}
else
{
lean_object* v_upperBound_1525_; lean_object* v_val_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1561_; 
v_upperBound_1525_ = lean_ctor_get(v_snd_1515_, 1);
v_val_1526_ = lean_ctor_get(v_next_1524_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_next_1524_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1528_ = v_next_1524_;
v_isShared_1529_ = v_isSharedCheck_1561_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_val_1526_);
lean_dec(v_next_1524_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1561_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_nat_dec_lt(v_val_1526_, v_upperBound_1525_);
if (v___x_1530_ == 0)
{
lean_del_object(v___x_1528_);
lean_dec(v_val_1526_);
goto v___jp_1519_;
}
else
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1558_; 
lean_inc(v_upperBound_1525_);
lean_del_object(v___x_1517_);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_snd_1515_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; lean_object* v_unused_1560_; 
v_unused_1559_ = lean_ctor_get(v_snd_1515_, 1);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v_snd_1515_, 0);
lean_dec(v_unused_1560_);
v___x_1532_ = v_snd_1515_;
v_isShared_1533_ = v_isSharedCheck_1558_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_snd_1515_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1558_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_a_1534_ = lean_array_uget_borrowed(v_as_1498_, v_i_1500_);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v_val_1526_, v___x_1535_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1536_);
v___x_1538_ = v___x_1528_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1538_);
v___x_1540_ = v___x_1532_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_upperBound_1525_);
v___x_1540_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; 
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v_a_1534_);
v___x_1541_ = lean_infer_type(v_a_1534_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1544_ = l_Lean_Expr_isAppOf(v_a_1542_, v___x_1543_);
lean_dec(v_a_1542_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec(v_val_1526_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_fst_1514_);
lean_ctor_set(v___x_1545_, 1, v___x_1540_);
v_a_1508_ = v___x_1545_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_array_push(v_fst_1514_, v_val_1526_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1540_);
v_a_1508_ = v___x_1547_;
goto v___jp_1507_;
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v___x_1540_);
lean_dec(v_val_1526_);
lean_dec(v_fst_1514_);
v_a_1548_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1541_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1541_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
}
}
}
}
v___jp_1519_:
{
lean_object* v___x_1521_; 
if (v_isShared_1518_ == 0)
{
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_fst_1514_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_snd_1515_);
v___x_1521_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
}
}
v___jp_1507_:
{
size_t v___x_1509_; size_t v___x_1510_; 
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_add(v_i_1500_, v___x_1509_);
v_i_1500_ = v___x_1510_;
v_b_1501_ = v_a_1508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1563_, v_sz_boxed_1572_, v_i_boxed_1573_, v_b_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_as_1563_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1579_, lean_object* v_args_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___y_1589_; lean_object* v_env_1614_; lean_object* v___x_1615_; 
v___x_1587_ = lean_st_ref_get(v___y_1585_);
v_env_1614_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_ref(v_env_1614_);
lean_dec(v___x_1587_);
v___x_1615_ = l_Lean_getOutParamPositions_x3f(v_env_1614_, v_declName_1579_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1589_ = v___x_1616_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1617_; 
v_val_1617_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1615_, 1);
v___y_1589_ = v_val_1617_;
goto v___jp_1588_;
}
v___jp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; size_t v_sz_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1590_ = lean_array_get_size(v_args_1580_);
v___x_1591_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v___x_1590_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___y_1589_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v_sz_1594_ = lean_array_size(v_args_1580_);
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1580_, v_sz_1594_, v___x_1595_, v___x_1593_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_fst_1601_; lean_object* v___x_1603_; 
v_fst_1601_ = lean_ctor_get(v_a_1597_, 0);
lean_inc(v_fst_1601_);
lean_dec(v_a_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_fst_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_fst_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1606_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1596_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1596_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1618_, lean_object* v_args_1619_, lean_object* v_x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1618_, v_args_1619_, v_x_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v_x_1620_);
lean_dec_ref(v_args_1619_);
lean_dec(v_declName_1618_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_getAppFn(v_classTy_1627_);
if (lean_obj_tag(v___x_1633_) == 4)
{
lean_object* v_declName_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; 
v_declName_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_declName_1634_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1635_, 0, v_declName_1634_);
lean_inc(v_a_1631_);
lean_inc_ref(v_a_1630_);
lean_inc(v_a_1629_);
lean_inc_ref(v_a_1628_);
v___x_1636_ = lean_infer_type(v___x_1633_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = 0;
v___x_1639_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1637_, v___f_1635_, v___x_1638_, v___x_1638_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
return v___x_1639_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___f_1635_);
v_a_1640_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1636_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1636_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref(v___x_1633_);
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec_ref(v_classTy_1650_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1657_, lean_object* v_as_1658_, lean_object* v_j_1659_){
_start:
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = lean_array_get_size(v_as_1658_);
v___x_1661_ = lean_nat_dec_lt(v_j_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v_j_1659_);
v___x_1662_ = lean_box(0);
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_array_fget_borrowed(v_as_1658_, v_j_1659_);
v___x_1664_ = l_Lean_Expr_mvarId_x21(v___x_1663_);
v___x_1665_ = l_Lean_instBEqMVarId_beq(v___x_1664_, v_a_1657_);
lean_dec(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v_j_1659_, v___x_1666_);
lean_dec(v_j_1659_);
v_j_1659_ = v___x_1667_;
goto _start;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_j_1659_);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1670_, lean_object* v_as_1671_, lean_object* v_j_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1670_, v_as_1671_, v_j_1672_);
lean_dec_ref(v_as_1671_);
lean_dec(v_a_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v_ks_1678_; lean_object* v_vs_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1703_; 
v_ks_1678_ = lean_ctor_get(v_x_1674_, 0);
v_vs_1679_ = lean_ctor_get(v_x_1674_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1674_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1681_ = v_x_1674_;
v_isShared_1682_ = v_isSharedCheck_1703_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_vs_1679_);
lean_inc(v_ks_1678_);
lean_dec(v_x_1674_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1703_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = lean_array_get_size(v_ks_1678_);
v___x_1684_ = lean_nat_dec_lt(v_x_1675_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_dec(v_x_1675_);
v___x_1685_ = lean_array_push(v_ks_1678_, v_x_1676_);
v___x_1686_ = lean_array_push(v_vs_1679_, v_x_1677_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1686_);
lean_ctor_set(v___x_1681_, 0, v___x_1685_);
v___x_1688_ = v___x_1681_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
else
{
lean_object* v_k_x27_1690_; uint8_t v___x_1691_; 
v_k_x27_1690_ = lean_array_fget_borrowed(v_ks_1678_, v_x_1675_);
v___x_1691_ = l_Lean_instBEqMVarId_beq(v_x_1676_, v_k_x27_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1693_; 
if (v_isShared_1682_ == 0)
{
v___x_1693_ = v___x_1681_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_ks_1678_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_vs_1679_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_nat_add(v_x_1675_, v___x_1694_);
lean_dec(v_x_1675_);
v_x_1674_ = v___x_1693_;
v_x_1675_ = v___x_1695_;
goto _start;
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = lean_array_fset(v_ks_1678_, v_x_1675_, v_x_1676_);
v___x_1699_ = lean_array_fset(v_vs_1679_, v_x_1675_, v_x_1677_);
lean_dec(v_x_1675_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1699_);
lean_ctor_set(v___x_1681_, 0, v___x_1698_);
v___x_1701_ = v___x_1681_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1704_, lean_object* v_k_1705_, lean_object* v_v_1706_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1704_, v___x_1707_, v_k_1705_, v_v_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1709_, size_t v_x_1710_, size_t v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v_es_1714_; size_t v___x_1715_; size_t v___x_1716_; lean_object* v_j_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_es_1714_ = lean_ctor_get(v_x_1709_, 0);
v___x_1715_ = ((size_t)31ULL);
v___x_1716_ = lean_usize_land(v_x_1710_, v___x_1715_);
v_j_1717_ = lean_usize_to_nat(v___x_1716_);
v___x_1718_ = lean_array_get_size(v_es_1714_);
v___x_1719_ = lean_nat_dec_lt(v_j_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec(v_j_1717_);
lean_dec(v_x_1713_);
lean_dec(v_x_1712_);
return v_x_1709_;
}
else
{
lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1758_; 
lean_inc_ref(v_es_1714_);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v_x_1709_, 0);
lean_dec(v_unused_1759_);
v___x_1721_ = v_x_1709_;
v_isShared_1722_ = v_isSharedCheck_1758_;
goto v_resetjp_1720_;
}
else
{
lean_dec(v_x_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1758_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_v_1723_; lean_object* v___x_1724_; lean_object* v_xs_x27_1725_; lean_object* v___y_1727_; 
v_v_1723_ = lean_array_fget(v_es_1714_, v_j_1717_);
v___x_1724_ = lean_box(0);
v_xs_x27_1725_ = lean_array_fset(v_es_1714_, v_j_1717_, v___x_1724_);
switch(lean_obj_tag(v_v_1723_))
{
case 0:
{
lean_object* v_key_1732_; lean_object* v_val_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1743_; 
v_key_1732_ = lean_ctor_get(v_v_1723_, 0);
v_val_1733_ = lean_ctor_get(v_v_1723_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_v_1723_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1735_ = v_v_1723_;
v_isShared_1736_ = v_isSharedCheck_1743_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_val_1733_);
lean_inc(v_key_1732_);
lean_dec(v_v_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1743_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Lean_instBEqMVarId_beq(v_x_1712_, v_key_1732_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_del_object(v___x_1735_);
v___x_1738_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1732_, v_val_1733_, v_x_1712_, v_x_1713_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___y_1727_ = v___x_1739_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1741_; 
lean_dec(v_val_1733_);
lean_dec(v_key_1732_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v_x_1713_);
lean_ctor_set(v___x_1735_, 0, v_x_1712_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_x_1712_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_x_1713_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
v___y_1727_ = v___x_1741_;
goto v___jp_1726_;
}
}
}
}
case 1:
{
lean_object* v_node_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1756_; 
v_node_1744_ = lean_ctor_get(v_v_1723_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_v_1723_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1746_ = v_v_1723_;
v_isShared_1747_ = v_isSharedCheck_1756_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_node_1744_);
lean_dec(v_v_1723_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1756_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
size_t v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1748_ = ((size_t)5ULL);
v___x_1749_ = lean_usize_shift_right(v_x_1710_, v___x_1748_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_x_1711_, v___x_1750_);
v___x_1752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1744_, v___x_1749_, v___x_1751_, v_x_1712_, v_x_1713_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1752_);
v___x_1754_ = v___x_1746_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
v___y_1727_ = v___x_1754_;
goto v___jp_1726_;
}
}
}
default: 
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_x_1712_);
lean_ctor_set(v___x_1757_, 1, v_x_1713_);
v___y_1727_ = v___x_1757_;
goto v___jp_1726_;
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_array_fset(v_xs_x27_1725_, v_j_1717_, v___y_1727_);
lean_dec(v_j_1717_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1728_);
v___x_1730_ = v___x_1721_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
else
{
lean_object* v_ks_1760_; lean_object* v_vs_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1779_; 
v_ks_1760_ = lean_ctor_get(v_x_1709_, 0);
v_vs_1761_ = lean_ctor_get(v_x_1709_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1763_ = v_x_1709_;
v_isShared_1764_ = v_isSharedCheck_1779_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_vs_1761_);
lean_inc(v_ks_1760_);
lean_dec(v_x_1709_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1779_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_ks_1760_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_vs_1761_);
v___x_1766_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_newNode_1767_; size_t v___x_1768_; uint8_t v___x_1769_; 
v_newNode_1767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1766_, v_x_1712_, v_x_1713_);
v___x_1768_ = ((size_t)7ULL);
v___x_1769_ = lean_usize_dec_le(v___x_1768_, v_x_1711_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1767_);
v___x_1771_ = lean_unsigned_to_nat(4u);
v___x_1772_ = lean_nat_dec_lt(v___x_1770_, v___x_1771_);
lean_dec(v___x_1770_);
if (v___x_1772_ == 0)
{
lean_object* v_ks_1773_; lean_object* v_vs_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_ks_1773_ = lean_ctor_get(v_newNode_1767_, 0);
lean_inc_ref(v_ks_1773_);
v_vs_1774_ = lean_ctor_get(v_newNode_1767_, 1);
lean_inc_ref(v_vs_1774_);
lean_dec_ref(v_newNode_1767_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_1777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1711_, v_ks_1773_, v_vs_1774_, v___x_1775_, v___x_1776_);
lean_dec_ref(v_vs_1774_);
lean_dec_ref(v_ks_1773_);
return v___x_1777_;
}
else
{
return v_newNode_1767_;
}
}
else
{
return v_newNode_1767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1780_, lean_object* v_keys_1781_, lean_object* v_vals_1782_, lean_object* v_i_1783_, lean_object* v_entries_1784_){
_start:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_array_get_size(v_keys_1781_);
v___x_1786_ = lean_nat_dec_lt(v_i_1783_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec(v_i_1783_);
return v_entries_1784_;
}
else
{
lean_object* v_k_1787_; lean_object* v_v_1788_; uint64_t v___x_1789_; size_t v_h_1790_; size_t v___x_1791_; lean_object* v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; size_t v_h_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_k_1787_ = lean_array_fget_borrowed(v_keys_1781_, v_i_1783_);
v_v_1788_ = lean_array_fget_borrowed(v_vals_1782_, v_i_1783_);
v___x_1789_ = l_Lean_instHashableMVarId_hash(v_k_1787_);
v_h_1790_ = lean_uint64_to_usize(v___x_1789_);
v___x_1791_ = ((size_t)5ULL);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_sub(v_depth_1780_, v___x_1793_);
v___x_1795_ = lean_usize_mul(v___x_1791_, v___x_1794_);
v_h_1796_ = lean_usize_shift_right(v_h_1790_, v___x_1795_);
v___x_1797_ = lean_nat_add(v_i_1783_, v___x_1792_);
lean_dec(v_i_1783_);
lean_inc(v_v_1788_);
lean_inc(v_k_1787_);
v___x_1798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1784_, v_h_1796_, v_depth_1780_, v_k_1787_, v_v_1788_);
v_i_1783_ = v___x_1797_;
v_entries_1784_ = v___x_1798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1800_, lean_object* v_keys_1801_, lean_object* v_vals_1802_, lean_object* v_i_1803_, lean_object* v_entries_1804_){
_start:
{
size_t v_depth_boxed_1805_; lean_object* v_res_1806_; 
v_depth_boxed_1805_ = lean_unbox_usize(v_depth_1800_);
lean_dec(v_depth_1800_);
v_res_1806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1805_, v_keys_1801_, v_vals_1802_, v_i_1803_, v_entries_1804_);
lean_dec_ref(v_vals_1802_);
lean_dec_ref(v_keys_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
size_t v_x_1611__boxed_1812_; size_t v_x_1612__boxed_1813_; lean_object* v_res_1814_; 
v_x_1611__boxed_1812_ = lean_unbox_usize(v_x_1808_);
lean_dec(v_x_1808_);
v_x_1612__boxed_1813_ = lean_unbox_usize(v_x_1809_);
lean_dec(v_x_1809_);
v_res_1814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1807_, v_x_1611__boxed_1812_, v_x_1612__boxed_1813_, v_x_1810_, v_x_1811_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
uint64_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = l_Lean_instHashableMVarId_hash(v_x_1816_);
v___x_1819_ = lean_uint64_to_usize(v___x_1818_);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1815_, v___x_1819_, v___x_1820_, v_x_1816_, v_x_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1822_, lean_object* v_val_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v_mctx_1827_; lean_object* v_cache_1828_; lean_object* v_zetaDeltaFVarIds_1829_; lean_object* v_postponed_1830_; lean_object* v_diag_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1861_; 
v___x_1826_ = lean_st_ref_take(v___y_1824_);
v_mctx_1827_ = lean_ctor_get(v___x_1826_, 0);
v_cache_1828_ = lean_ctor_get(v___x_1826_, 1);
v_zetaDeltaFVarIds_1829_ = lean_ctor_get(v___x_1826_, 2);
v_postponed_1830_ = lean_ctor_get(v___x_1826_, 3);
v_diag_1831_ = lean_ctor_get(v___x_1826_, 4);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1833_ = v___x_1826_;
v_isShared_1834_ = v_isSharedCheck_1861_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_diag_1831_);
lean_inc(v_postponed_1830_);
lean_inc(v_zetaDeltaFVarIds_1829_);
lean_inc(v_cache_1828_);
lean_inc(v_mctx_1827_);
lean_dec(v___x_1826_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1861_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_depth_1835_; lean_object* v_levelAssignDepth_1836_; lean_object* v_lmvarCounter_1837_; lean_object* v_mvarCounter_1838_; lean_object* v_lDecls_1839_; lean_object* v_decls_1840_; lean_object* v_userNames_1841_; lean_object* v_lAssignment_1842_; lean_object* v_eAssignment_1843_; lean_object* v_dAssignment_1844_; lean_object* v_instanceTypedMVars_1845_; lean_object* v_synthNormMemo_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1860_; 
v_depth_1835_ = lean_ctor_get(v_mctx_1827_, 0);
v_levelAssignDepth_1836_ = lean_ctor_get(v_mctx_1827_, 1);
v_lmvarCounter_1837_ = lean_ctor_get(v_mctx_1827_, 2);
v_mvarCounter_1838_ = lean_ctor_get(v_mctx_1827_, 3);
v_lDecls_1839_ = lean_ctor_get(v_mctx_1827_, 4);
v_decls_1840_ = lean_ctor_get(v_mctx_1827_, 5);
v_userNames_1841_ = lean_ctor_get(v_mctx_1827_, 6);
v_lAssignment_1842_ = lean_ctor_get(v_mctx_1827_, 7);
v_eAssignment_1843_ = lean_ctor_get(v_mctx_1827_, 8);
v_dAssignment_1844_ = lean_ctor_get(v_mctx_1827_, 9);
v_instanceTypedMVars_1845_ = lean_ctor_get(v_mctx_1827_, 10);
v_synthNormMemo_1846_ = lean_ctor_get(v_mctx_1827_, 11);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_mctx_1827_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1848_ = v_mctx_1827_;
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_synthNormMemo_1846_);
lean_inc(v_instanceTypedMVars_1845_);
lean_inc(v_dAssignment_1844_);
lean_inc(v_eAssignment_1843_);
lean_inc(v_lAssignment_1842_);
lean_inc(v_userNames_1841_);
lean_inc(v_decls_1840_);
lean_inc(v_lDecls_1839_);
lean_inc(v_mvarCounter_1838_);
lean_inc(v_lmvarCounter_1837_);
lean_inc(v_levelAssignDepth_1836_);
lean_inc(v_depth_1835_);
lean_dec(v_mctx_1827_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1843_, v_mvarId_1822_, v_val_1823_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 8, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_depth_1835_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_levelAssignDepth_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_lmvarCounter_1837_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_mvarCounter_1838_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_lDecls_1839_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v_decls_1840_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_userNames_1841_);
lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_lAssignment_1842_);
lean_ctor_set(v_reuseFailAlloc_1859_, 8, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1859_, 9, v_dAssignment_1844_);
lean_ctor_set(v_reuseFailAlloc_1859_, 10, v_instanceTypedMVars_1845_);
lean_ctor_set(v_reuseFailAlloc_1859_, 11, v_synthNormMemo_1846_);
v___x_1853_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1853_);
v___x_1855_ = v___x_1833_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_cache_1828_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_zetaDeltaFVarIds_1829_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_postponed_1830_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_diag_1831_);
v___x_1855_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_st_ref_put(v___y_1824_, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1850_);
return v___x_1857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1862_, lean_object* v_val_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1862_, v_val_1863_, v___y_1864_);
lean_dec(v___y_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1867_, lean_object* v_argVars_1868_, lean_object* v_as_1869_, size_t v_sz_1870_, size_t v_i_1871_, lean_object* v_b_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_usize_dec_lt(v_i_1871_, v_sz_1870_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_b_1872_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v_a_1881_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1880_ = lean_box(0);
v_a_1881_ = lean_array_uget_borrowed(v_as_1869_, v_i_1871_);
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1881_, v_argMVars_1867_, v___x_1902_);
if (lean_obj_tag(v___x_1903_) == 1)
{
lean_object* v_val_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_val_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = l_Lean_instInhabitedExpr;
v___x_1906_ = lean_array_get_borrowed(v___x_1905_, v_argVars_1868_, v_val_1904_);
lean_dec(v_val_1904_);
lean_inc(v___x_1906_);
lean_inc(v_a_1881_);
v___x_1907_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1881_, v___x_1906_, v___y_1874_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec_ref_known(v___x_1907_, 1);
v___y_1883_ = v___y_1873_;
v___y_1884_ = v___y_1874_;
v___y_1885_ = v___y_1875_;
v___y_1886_ = v___y_1876_;
goto v___jp_1882_;
}
else
{
return v___x_1907_;
}
}
else
{
lean_dec(v___x_1903_);
v___y_1883_ = v___y_1873_;
v___y_1884_ = v___y_1874_;
v___y_1885_ = v___y_1875_;
v___y_1886_ = v___y_1876_;
goto v___jp_1882_;
}
v___jp_1882_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_inc(v_a_1881_);
v___x_1887_ = l_Lean_Expr_mvar___override(v_a_1881_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
v___x_1888_ = lean_infer_type(v___x_1887_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1867_, v_argVars_1868_, v_a_1889_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1890_) == 0)
{
size_t v___x_1891_; size_t v___x_1892_; 
lean_dec_ref_known(v___x_1890_, 1);
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_add(v_i_1871_, v___x_1891_);
v_i_1871_ = v___x_1892_;
v_b_1872_ = v___x_1880_;
goto _start;
}
else
{
return v___x_1890_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1888_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1888_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1908_, lean_object* v_argVars_1909_, lean_object* v_e_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Meta_getMVars(v_e_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; size_t v_sz_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = lean_box(0);
v_sz_1919_ = lean_array_size(v_a_1917_);
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1908_, v_argVars_1909_, v_a_1917_, v_sz_1919_, v___x_1920_, v___x_1918_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1917_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1921_, 0);
lean_dec(v_unused_1929_);
v___x_1923_ = v___x_1921_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_dec(v___x_1921_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1918_);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1918_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
return v___x_1921_;
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1916_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1916_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1938_, lean_object* v_argVars_1939_, lean_object* v_e_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1938_, v_argVars_1939_, v_e_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec_ref(v_argVars_1939_);
lean_dec_ref(v_argMVars_1938_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1947_, lean_object* v_argVars_1948_, lean_object* v_as_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_b_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
size_t v_sz_boxed_1958_; size_t v_i_boxed_1959_; lean_object* v_res_1960_; 
v_sz_boxed_1958_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1959_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1947_, v_argVars_1948_, v_as_1949_, v_sz_boxed_1958_, v_i_boxed_1959_, v_b_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v_as_1949_);
lean_dec_ref(v_argVars_1948_);
lean_dec_ref(v_argMVars_1947_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1961_, lean_object* v_val_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1961_, v_val_1962_, v___y_1964_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1969_, lean_object* v_val_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1969_, v_val_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1978_, v_x_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, size_t v_x_1984_, size_t v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1983_, v_x_1984_, v_x_1985_, v_x_1986_, v_x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
size_t v_x_1969__boxed_1995_; size_t v_x_1970__boxed_1996_; lean_object* v_res_1997_; 
v_x_1969__boxed_1995_ = lean_unbox_usize(v_x_1991_);
lean_dec(v_x_1991_);
v_x_1970__boxed_1996_ = lean_unbox_usize(v_x_1992_);
lean_dec(v_x_1992_);
v_res_1997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1989_, v_x_1990_, v_x_1969__boxed_1995_, v_x_1970__boxed_1996_, v_x_1993_, v_x_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1998_, lean_object* v_n_1999_, lean_object* v_k_2000_, lean_object* v_v_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1999_, v_k_2000_, v_v_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2003_, size_t v_depth_2004_, lean_object* v_keys_2005_, lean_object* v_vals_2006_, lean_object* v_heq_2007_, lean_object* v_i_2008_, lean_object* v_entries_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_2004_, v_keys_2005_, v_vals_2006_, v_i_2008_, v_entries_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2011_, lean_object* v_depth_2012_, lean_object* v_keys_2013_, lean_object* v_vals_2014_, lean_object* v_heq_2015_, lean_object* v_i_2016_, lean_object* v_entries_2017_){
_start:
{
size_t v_depth_boxed_2018_; lean_object* v_res_2019_; 
v_depth_boxed_2018_ = lean_unbox_usize(v_depth_2012_);
lean_dec(v_depth_2012_);
v_res_2019_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_2011_, v_depth_boxed_2018_, v_keys_2013_, v_vals_2014_, v_heq_2015_, v_i_2016_, v_entries_2017_);
lean_dec_ref(v_vals_2014_);
lean_dec_ref(v_keys_2013_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2021_, v_x_2022_, v_x_2023_, v_x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = l_Lean_Expr_hasMVar(v_e_2026_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_e_2026_);
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; lean_object* v_mctx_2032_; lean_object* v___x_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2036_; lean_object* v_cache_2037_; lean_object* v_zetaDeltaFVarIds_2038_; lean_object* v_postponed_2039_; lean_object* v_diag_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2049_; 
v___x_2031_ = lean_st_ref_get(v___y_2027_);
v_mctx_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_mctx_2032_);
lean_dec(v___x_2031_);
v___x_2033_ = l_Lean_instantiateMVarsCore(v_mctx_2032_, v_e_2026_);
v_fst_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_fst_2034_);
v_snd_2035_ = lean_ctor_get(v___x_2033_, 1);
lean_inc(v_snd_2035_);
lean_dec_ref(v___x_2033_);
v___x_2036_ = lean_st_ref_take(v___y_2027_);
v_cache_2037_ = lean_ctor_get(v___x_2036_, 1);
v_zetaDeltaFVarIds_2038_ = lean_ctor_get(v___x_2036_, 2);
v_postponed_2039_ = lean_ctor_get(v___x_2036_, 3);
v_diag_2040_ = lean_ctor_get(v___x_2036_, 4);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2050_);
v___x_2042_ = v___x_2036_;
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_diag_2040_);
lean_inc(v_postponed_2039_);
lean_inc(v_zetaDeltaFVarIds_2038_);
lean_inc(v_cache_2037_);
lean_dec(v___x_2036_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v_snd_2035_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_snd_2035_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_cache_2037_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_zetaDeltaFVarIds_2038_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_postponed_2039_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_diag_2040_);
v___x_2045_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_st_ref_put(v___y_2027_, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_fst_2034_);
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2051_, v___y_2052_);
lean_dec(v___y_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2055_, v___y_2057_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_2069_, lean_object* v_opt_2070_){
_start:
{
lean_object* v_name_2071_; lean_object* v_defValue_2072_; lean_object* v_map_2073_; lean_object* v___x_2074_; 
v_name_2071_ = lean_ctor_get(v_opt_2070_, 0);
v_defValue_2072_ = lean_ctor_get(v_opt_2070_, 1);
v_map_2073_ = lean_ctor_get(v_opts_2069_, 0);
v___x_2074_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2073_, v_name_2071_);
if (lean_obj_tag(v___x_2074_) == 0)
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_unbox(v_defValue_2072_);
return v___x_2075_;
}
else
{
lean_object* v_val_2076_; 
v_val_2076_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v___x_2074_, 1);
if (lean_obj_tag(v_val_2076_) == 1)
{
uint8_t v_v_2077_; 
v_v_2077_ = lean_ctor_get_uint8(v_val_2076_, 0);
lean_dec_ref_known(v_val_2076_, 0);
return v_v_2077_;
}
else
{
uint8_t v___x_2078_; 
lean_dec(v_val_2076_);
v___x_2078_ = lean_unbox(v_defValue_2072_);
return v___x_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_2079_, lean_object* v_opt_2080_){
_start:
{
uint8_t v_res_2081_; lean_object* v_r_2082_; 
v_res_2081_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_2079_, v_opt_2080_);
lean_dec_ref(v_opt_2080_);
lean_dec_ref(v_opts_2079_);
v_r_2082_ = lean_box(v_res_2081_);
return v_r_2082_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_2083_, lean_object* v_as_2084_, size_t v_i_2085_, size_t v_stop_2086_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_eq(v_i_2085_, v_stop_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_array_uget_borrowed(v_as_2084_, v_i_2085_);
v___x_2089_ = lean_nat_dec_eq(v_a_2083_, v___x_2088_);
if (v___x_2089_ == 0)
{
size_t v___x_2090_; size_t v___x_2091_; 
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2085_, v___x_2090_);
v_i_2085_ = v___x_2091_;
goto _start;
}
else
{
return v___x_2089_;
}
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = 0;
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_2094_, lean_object* v_as_2095_, lean_object* v_i_2096_, lean_object* v_stop_2097_){
_start:
{
size_t v_i_boxed_2098_; size_t v_stop_boxed_2099_; uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_i_boxed_2098_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_stop_boxed_2099_ = lean_unbox_usize(v_stop_2097_);
lean_dec(v_stop_2097_);
v_res_2100_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2094_, v_as_2095_, v_i_boxed_2098_, v_stop_boxed_2099_);
lean_dec_ref(v_as_2095_);
lean_dec(v_a_2094_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = lean_array_get_size(v_as_2102_);
v___x_2106_ = lean_nat_dec_lt(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
return v___x_2106_;
}
else
{
if (v___x_2106_ == 0)
{
return v___x_2106_;
}
else
{
size_t v___x_2107_; size_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2105_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2103_, v_as_2102_, v___x_2107_, v___x_2108_);
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_2110_, lean_object* v_a_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_as_2110_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2114_, lean_object* v_fst_2115_, lean_object* v_argVars_2116_, lean_object* v_as_2117_, size_t v_sz_2118_, size_t v_i_2119_, lean_object* v_b_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_a_2127_; uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_lt(v_i_2119_, v_sz_2118_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_b_2120_);
return v___x_2132_;
}
else
{
lean_object* v_next_2133_; 
v_next_2133_ = lean_ctor_get(v_b_2120_, 0);
lean_inc(v_next_2133_);
if (lean_obj_tag(v_next_2133_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_b_2120_);
return v___x_2134_;
}
else
{
lean_object* v_upperBound_2135_; lean_object* v_val_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2167_; 
v_upperBound_2135_ = lean_ctor_get(v_b_2120_, 1);
v_val_2136_ = lean_ctor_get(v_next_2133_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_next_2133_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2138_ = v_next_2133_;
v_isShared_2139_ = v_isSharedCheck_2167_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_val_2136_);
lean_dec(v_next_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2167_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_lt(v_val_2136_, v_upperBound_2135_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_del_object(v___x_2138_);
lean_dec(v_val_2136_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_b_2120_);
return v___x_2141_;
}
else
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2164_; 
lean_inc(v_upperBound_2135_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_b_2120_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2165_ = lean_ctor_get(v_b_2120_, 1);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_b_2120_, 0);
lean_dec(v_unused_2166_);
v___x_2143_ = v_b_2120_;
v_isShared_2144_ = v_isSharedCheck_2164_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v_b_2120_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2164_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_val_2136_, v___x_2145_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2146_);
v___x_2148_ = v___x_2138_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2148_);
v___x_2150_ = v___x_2143_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_upperBound_2135_);
v___x_2150_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
uint8_t v___x_2151_; 
v___x_2151_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2114_, v_val_2136_);
lean_dec(v_val_2136_);
if (v___x_2151_ == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_array_uget_borrowed(v_as_2117_, v_i_2119_);
lean_inc(v_a_2152_);
v___x_2153_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2115_, v_argVars_2116_, v_a_2152_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_dec_ref_known(v___x_2153_, 1);
v_a_2127_ = v___x_2150_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___x_2150_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
v_a_2127_ = v___x_2150_;
goto v___jp_2126_;
}
}
}
}
}
}
}
}
v___jp_2126_:
{
size_t v___x_2128_; size_t v___x_2129_; 
v___x_2128_ = ((size_t)1ULL);
v___x_2129_ = lean_usize_add(v_i_2119_, v___x_2128_);
v_i_2119_ = v___x_2129_;
v_b_2120_ = v_a_2127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2168_, lean_object* v_fst_2169_, lean_object* v_argVars_2170_, lean_object* v_as_2171_, lean_object* v_sz_2172_, lean_object* v_i_2173_, lean_object* v_b_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2172_);
lean_dec(v_sz_2172_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2168_, v_fst_2169_, v_argVars_2170_, v_as_2171_, v_sz_boxed_2180_, v_i_boxed_2181_, v_b_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec_ref(v_as_2171_);
lean_dec_ref(v_argVars_2170_);
lean_dec_ref(v_fst_2169_);
lean_dec_ref(v_a_2168_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2183_, lean_object* v_a_2184_, lean_object* v___x_2185_, lean_object* v_a_2186_, lean_object* v_b_2187_){
_start:
{
uint8_t v___x_2189_; 
v___x_2189_ = lean_nat_dec_lt(v_a_2186_, v_upperBound_2183_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
lean_dec(v_a_2186_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_b_2187_);
return v___x_2190_;
}
else
{
lean_object* v_snd_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2231_; 
v_snd_2191_ = lean_ctor_get(v_b_2187_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_b_2187_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v_b_2187_, 0);
lean_dec(v_unused_2232_);
v___x_2193_ = v_b_2187_;
v_isShared_2194_ = v_isSharedCheck_2231_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_snd_2191_);
lean_dec(v_b_2187_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2231_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_array_2195_; lean_object* v_start_2196_; lean_object* v_stop_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_array_2195_ = lean_ctor_get(v_snd_2191_, 0);
v_start_2196_ = lean_ctor_get(v_snd_2191_, 1);
v_stop_2197_ = lean_ctor_get(v_snd_2191_, 2);
v___x_2198_ = lean_box(0);
v___x_2199_ = lean_nat_dec_lt(v_start_2196_, v_stop_2197_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2201_; 
lean_dec(v_a_2186_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2198_);
v___x_2201_ = v___x_2193_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_snd_2191_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
else
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2227_; 
lean_inc(v_stop_2197_);
lean_inc(v_start_2196_);
lean_inc_ref(v_array_2195_);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_snd_2191_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; lean_object* v_unused_2230_; 
v_unused_2228_ = lean_ctor_get(v_snd_2191_, 2);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_snd_2191_, 1);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_snd_2191_, 0);
lean_dec(v_unused_2230_);
v___x_2205_ = v_snd_2191_;
v_isShared_2206_ = v_isSharedCheck_2227_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v_snd_2191_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2227_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2207_ = lean_array_fget(v_array_2195_, v_start_2196_);
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_add(v_start_2196_, v___x_2208_);
lean_dec(v_start_2196_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___x_2209_);
v___x_2211_ = v___x_2205_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_array_2195_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_stop_2197_);
v___x_2211_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
uint8_t v___x_2218_; 
v___x_2218_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2184_, v_a_2186_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; 
v___x_2219_ = l_Lean_Expr_hasExprMVar(v___x_2207_);
lean_dec(v___x_2207_);
if (v___x_2219_ == 0)
{
goto v___jp_2212_;
}
else
{
lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_del_object(v___x_2193_);
lean_dec(v_a_2186_);
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_nat_dec_eq(v___x_2185_, v___x_2220_);
v___x_2222_ = lean_box(v___x_2221_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___x_2211_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
else
{
lean_dec(v___x_2207_);
goto v___jp_2212_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 1, v___x_2211_);
lean_ctor_set(v___x_2193_, 0, v___x_2198_);
v___x_2214_ = v___x_2193_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2211_);
v___x_2214_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_nat_add(v_a_2186_, v___x_2208_);
lean_dec(v_a_2186_);
v_a_2186_ = v___x_2215_;
v_b_2187_ = v___x_2214_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2233_, lean_object* v_a_2234_, lean_object* v___x_2235_, lean_object* v_a_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2233_, v_a_2234_, v___x_2235_, v_a_2236_, v_b_2237_);
lean_dec(v___x_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_upperBound_2233_);
return v_res_2239_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2240_; lean_object* v_dummy_2241_; 
v___x_2240_ = lean_box(0);
v_dummy_2241_ = l_Lean_Expr_sort___override(v___x_2240_);
return v_dummy_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2242_, lean_object* v___x_2243_, uint8_t v___x_2244_, lean_object* v_x_2245_, lean_object* v_argTy_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
v___x_2252_ = lean_whnf(v_argTy_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2254_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2253_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v_dummy_2256_; lean_object* v_nargs_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v_dummy_2256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2257_ = l_Lean_Expr_getAppNumArgs(v_a_2253_);
lean_inc(v_nargs_2257_);
v___x_2258_ = lean_mk_array(v_nargs_2257_, v_dummy_2256_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_sub(v_nargs_2257_, v___x_2259_);
lean_dec(v_nargs_2257_);
v___x_2261_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2253_, v___x_2258_, v___x_2260_);
v___x_2262_ = lean_array_get_size(v___x_2261_);
lean_inc(v___x_2242_);
v___x_2263_ = l_Array_toSubarray___redArg(v___x_2261_, v___x_2242_, v___x_2262_);
v___x_2264_ = lean_box(0);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2263_);
v___x_2266_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2262_, v_a_2255_, v___x_2243_, v___x_2242_, v___x_2265_);
lean_dec(v_a_2255_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2280_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2280_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2280_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_fst_2271_; 
v_fst_2271_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_fst_2271_);
lean_dec(v_a_2267_);
if (lean_obj_tag(v_fst_2271_) == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(v___x_2244_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2272_);
v___x_2274_ = v___x_2269_;
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
lean_object* v_val_2276_; lean_object* v___x_2278_; 
v_val_2276_ = lean_ctor_get(v_fst_2271_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v_fst_2271_, 1);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v_val_2276_);
v___x_2278_ = v___x_2269_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_val_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2266_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2266_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_a_2253_);
lean_dec(v___x_2242_);
v_a_2289_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2254_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2254_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v___x_2242_);
v_a_2297_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2252_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2252_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2305_, lean_object* v___x_2306_, lean_object* v___x_2307_, lean_object* v_x_2308_, lean_object* v_argTy_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v___x_22652__boxed_2315_; lean_object* v_res_2316_; 
v___x_22652__boxed_2315_ = lean_unbox(v___x_2307_);
v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2305_, v___x_2306_, v___x_22652__boxed_2315_, v_x_2308_, v_argTy_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec_ref(v_x_2308_);
lean_dec(v___x_2306_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2320_, lean_object* v_projInfo_x3f_2321_, lean_object* v___x_2322_, lean_object* v_argVars_2323_, lean_object* v_as_2324_, size_t v_sz_2325_, size_t v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v___x_2333_; 
v___x_2333_ = lean_usize_dec_lt(v_i_2326_, v_sz_2325_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; 
lean_dec(v___x_2322_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_b_2327_);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___f_2340_; uint8_t v___x_2341_; lean_object* v_a_2342_; lean_object* v___y_2349_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_b_2327_);
v___x_2335_ = lean_box(0);
v___x_2336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2337_ = l_Lean_instInhabitedExpr;
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_box(v___x_2333_);
lean_inc(v___x_2322_);
v___f_2340_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2340_, 0, v___x_2338_);
lean_closure_set(v___f_2340_, 1, v___x_2322_);
lean_closure_set(v___f_2340_, 2, v___x_2339_);
v___x_2341_ = lean_nat_dec_eq(v___x_2322_, v___x_2338_);
v_a_2342_ = lean_array_uget_borrowed(v_as_2324_, v_i_2326_);
v___x_2363_ = lean_array_get_borrowed(v___x_2337_, v_fst_2320_, v_a_2342_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___x_2363_);
v___x_2364_ = lean_infer_type(v___x_2363_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2365_, v___y_2329_);
if (lean_obj_tag(v___x_2366_) == 0)
{
if (lean_obj_tag(v_projInfo_x3f_2321_) == 1)
{
lean_object* v_val_2367_; lean_object* v_a_2368_; lean_object* v_numParams_2369_; uint8_t v___x_2370_; 
v_val_2367_ = lean_ctor_get(v_projInfo_x3f_2321_, 0);
v_a_2368_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2366_, 1);
v_numParams_2369_ = lean_ctor_get(v_val_2367_, 1);
v___x_2370_ = lean_nat_dec_eq(v_numParams_2369_, v_a_2342_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2368_, v___f_2340_, v___x_2341_, v___x_2341_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
v___y_2349_ = v___x_2371_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2372_; 
lean_dec_ref(v___f_2340_);
lean_dec(v___x_2322_);
v___x_2372_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2320_, v_argVars_2323_, v_a_2368_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref_known(v___x_2372_, 1);
goto v___jp_2343_;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2382_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2381_, v___f_2340_, v___x_2341_, v___x_2341_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
v___y_2349_ = v___x_2382_;
goto v___jp_2348_;
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v___f_2340_);
lean_dec(v___x_2322_);
v_a_2383_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2366_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2366_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v___f_2340_);
lean_dec(v___x_2322_);
v_a_2391_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2364_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2364_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
v___jp_2343_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_inc(v_a_2342_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2342_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2335_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
v___jp_2348_:
{
if (lean_obj_tag(v___y_2349_) == 0)
{
lean_object* v_a_2350_; uint8_t v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___y_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___y_2349_, 1);
v___x_2351_ = lean_unbox(v_a_2350_);
lean_dec(v_a_2350_);
if (v___x_2351_ == 0)
{
size_t v___x_2352_; size_t v___x_2353_; 
v___x_2352_ = ((size_t)1ULL);
v___x_2353_ = lean_usize_add(v_i_2326_, v___x_2352_);
v_i_2326_ = v___x_2353_;
v_b_2327_ = v___x_2336_;
goto _start;
}
else
{
lean_dec(v___x_2322_);
goto v___jp_2343_;
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v___x_2322_);
v_a_2355_ = lean_ctor_get(v___y_2349_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___y_2349_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___y_2349_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___y_2349_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2399_, lean_object* v_projInfo_x3f_2400_, lean_object* v___x_2401_, lean_object* v_argVars_2402_, lean_object* v_as_2403_, lean_object* v_sz_2404_, lean_object* v_i_2405_, lean_object* v_b_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
size_t v_sz_boxed_2412_; size_t v_i_boxed_2413_; lean_object* v_res_2414_; 
v_sz_boxed_2412_ = lean_unbox_usize(v_sz_2404_);
lean_dec(v_sz_2404_);
v_i_boxed_2413_ = lean_unbox_usize(v_i_2405_);
lean_dec(v_i_2405_);
v_res_2414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2399_, v_projInfo_x3f_2400_, v___x_2401_, v_argVars_2402_, v_as_2403_, v_sz_boxed_2412_, v_i_boxed_2413_, v_b_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_as_2403_);
lean_dec_ref(v_argVars_2402_);
lean_dec(v_projInfo_x3f_2400_);
lean_dec_ref(v_fst_2399_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2415_, lean_object* v_as_2416_, size_t v_i_2417_, size_t v_stop_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v___y_2421_; uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_eq(v_i_2417_, v_stop_2418_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = lean_array_uget_borrowed(v_as_2416_, v_i_2417_);
v___x_2427_ = lean_nat_dec_eq(v___x_2426_, v_next_2415_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
lean_inc(v___x_2426_);
v___x_2428_ = lean_array_push(v_b_2419_, v___x_2426_);
v___y_2421_ = v___x_2428_;
goto v___jp_2420_;
}
else
{
v___y_2421_ = v_b_2419_;
goto v___jp_2420_;
}
}
else
{
return v_b_2419_;
}
v___jp_2420_:
{
size_t v___x_2422_; size_t v___x_2423_; 
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2417_, v___x_2422_);
v_i_2417_ = v___x_2423_;
v_b_2419_ = v___y_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2429_, lean_object* v_as_2430_, lean_object* v_i_2431_, lean_object* v_stop_2432_, lean_object* v_b_2433_){
_start:
{
size_t v_i_boxed_2434_; size_t v_stop_boxed_2435_; lean_object* v_res_2436_; 
v_i_boxed_2434_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_stop_boxed_2435_ = lean_unbox_usize(v_stop_2432_);
lean_dec(v_stop_2432_);
v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2429_, v_as_2430_, v_i_boxed_2434_, v_stop_boxed_2435_, v_b_2433_);
lean_dec_ref(v_as_2430_);
lean_dec(v_next_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2437_, lean_object* v___x_2438_, lean_object* v_fst_2439_, lean_object* v_argVars_2440_, lean_object* v_snd_2441_, lean_object* v_next_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; lean_object* v___y_2450_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
lean_inc(v_next_2442_);
v___x_2448_ = lean_array_push(v_fst_2437_, v_next_2442_);
v___x_2490_ = lean_unsigned_to_nat(0u);
v___x_2491_ = lean_array_get_size(v_snd_2441_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2493_ = lean_nat_dec_lt(v___x_2490_, v___x_2491_);
if (v___x_2493_ == 0)
{
v___y_2450_ = v___x_2492_;
goto v___jp_2449_;
}
else
{
uint8_t v___x_2494_; 
v___x_2494_ = lean_nat_dec_le(v___x_2491_, v___x_2491_);
if (v___x_2494_ == 0)
{
if (v___x_2493_ == 0)
{
v___y_2450_ = v___x_2492_;
goto v___jp_2449_;
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = lean_usize_of_nat(v___x_2491_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2442_, v_snd_2441_, v___x_2495_, v___x_2496_, v___x_2492_);
v___y_2450_ = v___x_2497_;
goto v___jp_2449_;
}
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2491_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2442_, v_snd_2441_, v___x_2498_, v___x_2499_, v___x_2492_);
v___y_2450_ = v___x_2500_;
goto v___jp_2449_;
}
}
v___jp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_array_get_borrowed(v___x_2438_, v_fst_2439_, v_next_2442_);
lean_dec(v_next_2442_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc(v___x_2451_);
v___x_2452_ = lean_infer_type(v___x_2451_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2439_, v_argVars_2440_, v_a_2453_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref_known(v___x_2454_, 1);
lean_inc(v___x_2451_);
v___x_2455_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2439_, v_argVars_2440_, v___x_2451_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2464_; 
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2465_);
v___x_2457_ = v___x_2455_;
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
else
{
lean_dec(v___x_2455_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2448_);
lean_ctor_set(v___x_2459_, 1, v___y_2450_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2460_);
v___x_2462_ = v___x_2457_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___x_2448_);
v_a_2466_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2455_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2455_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___x_2448_);
v_a_2474_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2454_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2454_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___x_2448_);
v_a_2482_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2452_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2452_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2501_, lean_object* v___x_2502_, lean_object* v_fst_2503_, lean_object* v_argVars_2504_, lean_object* v_snd_2505_, lean_object* v_next_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2501_, v___x_2502_, v_fst_2503_, v_argVars_2504_, v_snd_2505_, v_next_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v_snd_2505_);
lean_dec_ref(v_argVars_2504_);
lean_dec_ref(v_fst_2503_);
lean_dec_ref(v___x_2502_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; lean_object* v_env_2520_; uint8_t v___x_2521_; lean_object* v_env_2522_; lean_object* v___x_2523_; lean_object* v_toCold_2524_; lean_object* v_mctx_2525_; lean_object* v_lctx_2526_; lean_object* v_options_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2519_ = lean_st_ref_get(v___y_2517_);
v_env_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_env_2520_);
lean_dec(v___x_2519_);
v___x_2521_ = 0;
v_env_2522_ = l_Lean_Environment_setRecordingDeps(v_env_2520_, v___x_2521_);
v___x_2523_ = lean_st_ref_get(v___y_2515_);
v_toCold_2524_ = lean_ctor_get(v___y_2516_, 0);
v_mctx_2525_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_ref(v_mctx_2525_);
lean_dec(v___x_2523_);
v_lctx_2526_ = lean_ctor_get(v___y_2514_, 2);
v_options_2527_ = lean_ctor_get(v_toCold_2524_, 2);
lean_inc_ref(v_options_2527_);
lean_inc_ref(v_lctx_2526_);
v___x_2528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2528_, 0, v_env_2522_);
lean_ctor_set(v___x_2528_, 1, v_mctx_2525_);
lean_ctor_set(v___x_2528_, 2, v_lctx_2526_);
lean_ctor_set(v___x_2528_, 3, v_options_2527_);
v___x_2529_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v_msgData_2513_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_ref_2544_; lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2554_; 
v_ref_2544_ = lean_ctor_get(v___y_2541_, 2);
v___x_2545_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_inc(v_ref_2544_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_ref_2544_);
lean_ctor_set(v___x_2550_, 1, v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 1);
lean_ctor_set(v___x_2548_, 0, v___x_2550_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2562_, size_t v_sz_2563_, size_t v_i_2564_, lean_object* v_bs_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v___x_2571_; 
v___x_2571_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_bs_2565_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; lean_object* v_v_2574_; lean_object* v___x_2575_; lean_object* v_bs_x27_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2573_ = l_Lean_instInhabitedExpr;
v_v_2574_ = lean_array_uget(v_bs_2565_, v_i_2564_);
v___x_2575_ = lean_unsigned_to_nat(0u);
v_bs_x27_2576_ = lean_array_uset(v_bs_2565_, v_i_2564_, v___x_2575_);
v___x_2577_ = lean_array_get_borrowed(v___x_2573_, v_fst_2562_, v_v_2574_);
lean_dec(v_v_2574_);
lean_inc(v___y_2569_);
lean_inc_ref(v___y_2568_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___x_2577_);
v___x_2578_ = lean_infer_type(v___x_2577_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2580_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___x_2580_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2579_, v___y_2567_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = l_Lean_Expr_setPPExplicit(v_a_2581_, v___x_2571_);
v___x_2583_ = l_Lean_indentExpr(v___x_2582_);
v___x_2584_ = ((size_t)1ULL);
v___x_2585_ = lean_usize_add(v_i_2564_, v___x_2584_);
v___x_2586_ = lean_array_uset(v_bs_x27_2576_, v_i_2564_, v___x_2583_);
v_i_2564_ = v___x_2585_;
v_bs_2565_ = v___x_2586_;
goto _start;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_bs_x27_2576_);
v_a_2588_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2580_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2580_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec_ref(v_bs_x27_2576_);
v_a_2596_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2578_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2578_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2604_, lean_object* v_sz_2605_, lean_object* v_i_2606_, lean_object* v_bs_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
size_t v_sz_boxed_2613_; size_t v_i_boxed_2614_; lean_object* v_res_2615_; 
v_sz_boxed_2613_ = lean_unbox_usize(v_sz_2605_);
lean_dec(v_sz_2605_);
v_i_boxed_2614_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_res_2615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2604_, v_sz_boxed_2613_, v_i_boxed_2614_, v_bs_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v_fst_2604_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v___x_2616_, lean_object* v_snd_2617_, lean_object* v___f_2618_, lean_object* v_____r_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_array_get_borrowed(v___x_2616_, v_snd_2617_, v___x_2625_);
lean_inc(v___y_2623_);
lean_inc_ref(v___y_2622_);
lean_inc(v___y_2621_);
lean_inc_ref(v___y_2620_);
lean_inc(v___x_2626_);
v___x_2627_ = lean_apply_6(v___f_2618_, v___x_2626_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, lean_box(0));
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v___x_2628_, lean_object* v_snd_2629_, lean_object* v___f_2630_, lean_object* v_____r_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2628_, v_snd_2629_, v___f_2630_, v_____r_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v_snd_2629_);
lean_dec(v___x_2628_);
return v_res_2637_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2642_ = l_Lean_MessageData_ofFormat(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2652_, lean_object* v_argVars_2653_, lean_object* v_inst_2654_, lean_object* v_a_2655_, lean_object* v_projInfo_x3f_2656_, lean_object* v_a_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___y_2664_; lean_object* v_fst_2684_; lean_object* v_snd_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2757_; 
v_fst_2684_ = lean_ctor_get(v_a_2657_, 0);
v_snd_2685_ = lean_ctor_get(v_a_2657_, 1);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2687_ = v_a_2657_;
v_isShared_2688_ = v_isSharedCheck_2757_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snd_2685_);
lean_inc(v_fst_2684_);
lean_dec(v_a_2657_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2757_;
goto v_resetjp_2686_;
}
v___jp_2663_:
{
if (lean_obj_tag(v___y_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2675_; 
v_a_2665_ = lean_ctor_get(v___y_2664_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___y_2664_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2667_ = v___y_2664_;
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___y_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
if (lean_obj_tag(v_a_2665_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; 
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_argVars_2653_);
lean_dec_ref(v_fst_2652_);
v_a_2669_ = lean_ctor_get(v_a_2665_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v_a_2665_, 1);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v_a_2669_);
v___x_2671_ = v___x_2667_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
else
{
lean_object* v_a_2673_; 
lean_del_object(v___x_2667_);
v_a_2673_ = lean_ctor_get(v_a_2665_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v_a_2665_, 1);
v_a_2657_ = v_a_2673_;
goto _start;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_argVars_2653_);
lean_dec_ref(v_fst_2652_);
v_a_2676_ = lean_ctor_get(v___y_2664_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___y_2664_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___y_2664_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___y_2664_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2689_ = lean_array_get_size(v_snd_2685_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = lean_nat_dec_eq(v___x_2689_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; lean_object* v___f_2693_; lean_object* v___x_2736_; size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
lean_del_object(v___x_2687_);
v___x_2692_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_2685_);
lean_inc_ref(v_argVars_2653_);
lean_inc_ref(v_fst_2652_);
lean_inc(v_fst_2684_);
v___f_2693_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2693_, 0, v_fst_2684_);
lean_closure_set(v___f_2693_, 1, v___x_2692_);
lean_closure_set(v___f_2693_, 2, v_fst_2652_);
lean_closure_set(v___f_2693_, 3, v_argVars_2653_);
lean_closure_set(v___f_2693_, 4, v_snd_2685_);
v___x_2736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2737_ = lean_array_size(v_snd_2685_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2652_, v_projInfo_x3f_2656_, v___x_2689_, v_argVars_2653_, v_snd_2685_, v_sz_2737_, v___x_2738_, v___x_2736_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v_fst_2741_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v_fst_2741_ = lean_ctor_get(v_a_2740_, 0);
lean_inc(v_fst_2741_);
lean_dec(v_a_2740_);
if (lean_obj_tag(v_fst_2741_) == 0)
{
lean_dec(v_fst_2684_);
goto v___jp_2694_;
}
else
{
lean_object* v_val_2742_; 
v_val_2742_ = lean_ctor_get(v_fst_2741_, 0);
lean_inc(v_val_2742_);
lean_dec_ref_known(v_fst_2741_, 1);
if (lean_obj_tag(v_val_2742_) == 0)
{
lean_dec(v_fst_2684_);
goto v___jp_2694_;
}
else
{
lean_object* v_val_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v___f_2693_);
v_val_2743_ = lean_ctor_get(v_val_2742_, 0);
lean_inc(v_val_2743_);
lean_dec_ref_known(v_val_2742_, 1);
v___x_2744_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2684_, v___x_2692_, v_fst_2652_, v_argVars_2653_, v_snd_2685_, v_val_2743_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v_snd_2685_);
v___y_2664_ = v___x_2744_;
goto v___jp_2663_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___f_2693_);
lean_dec(v_snd_2685_);
lean_dec(v_fst_2684_);
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_argVars_2653_);
lean_dec_ref(v_fst_2652_);
v_a_2745_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2739_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2739_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
v___jp_2694_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2695_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2660_);
v___x_2696_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2697_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_2695_, v___x_2696_);
lean_dec_ref(v___x_2695_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_box(0);
v___x_2699_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2690_, v_snd_2685_, v___f_2693_, v___x_2698_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v_snd_2685_);
v___y_2664_ = v___x_2699_;
goto v___jp_2663_;
}
else
{
size_t v_sz_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
v_sz_2700_ = lean_array_size(v_snd_2685_);
v___x_2701_ = ((size_t)0ULL);
lean_inc(v_snd_2685_);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2652_, v_sz_2700_, v___x_2701_, v_snd_2685_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = lean_array_to_list(v_a_2703_);
v___x_2705_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2706_ = l_Lean_MessageData_joinSep(v___x_2704_, v___x_2705_);
v___x_2707_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2654_);
v___x_2708_ = l_Lean_MessageData_ofExpr(v_inst_2654_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
lean_inc_ref(v_a_2655_);
v___x_2712_ = l_Lean_indentExpr(v_a_2655_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___x_2706_);
v___x_2717_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2716_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2690_, v_snd_2685_, v___f_2693_, v_a_2718_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v_snd_2685_);
v___y_2664_ = v___x_2719_;
goto v___jp_2663_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___f_2693_);
lean_dec(v_snd_2685_);
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_argVars_2653_);
lean_dec_ref(v_fst_2652_);
v_a_2720_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2717_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2717_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v___f_2693_);
lean_dec(v_snd_2685_);
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_argVars_2653_);
lean_dec_ref(v_fst_2652_);
v_a_2728_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2702_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2702_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
}
else
{
lean_object* v___x_2754_; 
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_inst_2654_);
lean_dec_ref(v_argVars_2653_);
lean_dec_ref(v_fst_2652_);
if (v_isShared_2688_ == 0)
{
v___x_2754_ = v___x_2687_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_fst_2684_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_snd_2685_);
v___x_2754_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
return v___x_2755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2758_, lean_object* v_argVars_2759_, lean_object* v_inst_2760_, lean_object* v_a_2761_, lean_object* v_projInfo_x3f_2762_, lean_object* v_a_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2758_, v_argVars_2759_, v_inst_2760_, v_a_2761_, v_projInfo_x3f_2762_, v_a_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v_projInfo_x3f_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
if (lean_obj_tag(v_a_2771_) == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l_List_reverse___redArg(v_a_2772_);
return v___x_2773_;
}
else
{
lean_object* v_head_2774_; lean_object* v_tail_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2790_; 
v_head_2774_ = lean_ctor_get(v_a_2771_, 0);
v_tail_2775_ = lean_ctor_get(v_a_2771_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_a_2771_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2777_ = v_a_2771_;
v_isShared_2778_ = v_isSharedCheck_2790_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_tail_2775_);
lean_inc(v_head_2774_);
lean_dec(v_a_2771_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2790_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; uint8_t v___x_2783_; uint8_t v___x_2784_; 
v___x_2779_ = 0;
v___x_2780_ = lean_box(v___x_2779_);
v___x_2781_ = lean_array_get(v___x_2780_, v_fst_2770_, v_head_2774_);
lean_dec(v___x_2780_);
v___x_2782_ = 3;
v___x_2783_ = lean_unbox(v___x_2781_);
lean_dec(v___x_2781_);
v___x_2784_ = l_Lean_instBEqBinderInfo_beq(v___x_2783_, v___x_2782_);
if (v___x_2784_ == 0)
{
lean_del_object(v___x_2777_);
lean_dec(v_head_2774_);
v_a_2771_ = v_tail_2775_;
goto _start;
}
else
{
lean_object* v___x_2787_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 1, v_a_2772_);
v___x_2787_ = v___x_2777_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_head_2774_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_a_2772_);
v___x_2787_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
v_a_2771_ = v_tail_2775_;
v_a_2772_ = v___x_2787_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2791_, v_a_2792_, v_a_2793_);
lean_dec_ref(v_fst_2791_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2795_, size_t v_sz_2796_, size_t v_i_2797_, lean_object* v_bs_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_lt(v_i_2797_, v_sz_2796_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_bs_2798_);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v_v_2807_; lean_object* v___x_2808_; lean_object* v_bs_x27_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2806_ = l_Lean_instInhabitedExpr;
v_v_2807_ = lean_array_uget(v_bs_2798_, v_i_2797_);
v___x_2808_ = lean_unsigned_to_nat(0u);
v_bs_x27_2809_ = lean_array_uset(v_bs_2798_, v_i_2797_, v___x_2808_);
v___x_2810_ = lean_array_get_borrowed(v___x_2806_, v_argVars_2795_, v_v_2807_);
lean_dec(v_v_2807_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc(v___x_2810_);
v___x_2811_ = lean_infer_type(v___x_2810_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2813_ = l_Lean_indentExpr(v_a_2812_);
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2797_, v___x_2814_);
v___x_2816_ = lean_array_uset(v_bs_x27_2809_, v_i_2797_, v___x_2813_);
v_i_2797_ = v___x_2815_;
v_bs_2798_ = v___x_2816_;
goto _start;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v_bs_x27_2809_);
v_a_2818_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2811_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2811_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2826_, lean_object* v_sz_2827_, lean_object* v_i_2828_, lean_object* v_bs_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
size_t v_sz_boxed_2835_; size_t v_i_boxed_2836_; lean_object* v_res_2837_; 
v_sz_boxed_2835_ = lean_unbox_usize(v_sz_2827_);
lean_dec(v_sz_2827_);
v_i_boxed_2836_ = lean_unbox_usize(v_i_2828_);
lean_dec(v_i_2828_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2826_, v_sz_boxed_2835_, v_i_boxed_2836_, v_bs_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v_argVars_2826_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
if (lean_obj_tag(v_a_2838_) == 0)
{
lean_object* v___x_2840_; 
v___x_2840_ = l_List_reverse___redArg(v_a_2839_);
return v___x_2840_;
}
else
{
lean_object* v_head_2841_; lean_object* v_tail_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2853_; 
v_head_2841_ = lean_ctor_get(v_a_2838_, 0);
v_tail_2842_ = lean_ctor_get(v_a_2838_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_a_2838_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2844_ = v_a_2838_;
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_tail_2842_);
lean_inc(v_head_2841_);
lean_dec(v_a_2838_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2846_ = l_Nat_reprFast(v_head_2841_);
v___x_2847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v___x_2848_ = l_Lean_MessageData_ofFormat(v___x_2847_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v_a_2839_);
lean_ctor_set(v___x_2844_, 0, v___x_2848_);
v___x_2850_ = v___x_2844_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_a_2839_);
v___x_2850_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v_a_2838_ = v_tail_2842_;
v_a_2839_ = v___x_2850_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2854_; double v___x_2855_; 
v___x_2854_ = lean_unsigned_to_nat(0u);
v___x_2855_ = lean_float_of_nat(v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2858_, lean_object* v_msg_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_ref_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2912_; 
v_ref_2865_ = lean_ctor_get(v___y_2862_, 2);
v___x_2866_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2912_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2912_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v_traceState_2872_; lean_object* v_env_2873_; lean_object* v_nextMacroScope_2874_; lean_object* v_ngen_2875_; lean_object* v_auxDeclNGen_2876_; lean_object* v_cache_2877_; lean_object* v_recordedDeps_2878_; lean_object* v_messages_2879_; lean_object* v_infoState_2880_; lean_object* v_snapshotTasks_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2911_; 
v___x_2871_ = lean_st_ref_take(v___y_2863_);
v_traceState_2872_ = lean_ctor_get(v___x_2871_, 4);
v_env_2873_ = lean_ctor_get(v___x_2871_, 0);
v_nextMacroScope_2874_ = lean_ctor_get(v___x_2871_, 1);
v_ngen_2875_ = lean_ctor_get(v___x_2871_, 2);
v_auxDeclNGen_2876_ = lean_ctor_get(v___x_2871_, 3);
v_cache_2877_ = lean_ctor_get(v___x_2871_, 5);
v_recordedDeps_2878_ = lean_ctor_get(v___x_2871_, 6);
v_messages_2879_ = lean_ctor_get(v___x_2871_, 7);
v_infoState_2880_ = lean_ctor_get(v___x_2871_, 8);
v_snapshotTasks_2881_ = lean_ctor_get(v___x_2871_, 9);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2883_ = v___x_2871_;
v_isShared_2884_ = v_isSharedCheck_2911_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_snapshotTasks_2881_);
lean_inc(v_infoState_2880_);
lean_inc(v_messages_2879_);
lean_inc(v_recordedDeps_2878_);
lean_inc(v_cache_2877_);
lean_inc(v_traceState_2872_);
lean_inc(v_auxDeclNGen_2876_);
lean_inc(v_ngen_2875_);
lean_inc(v_nextMacroScope_2874_);
lean_inc(v_env_2873_);
lean_dec(v___x_2871_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2911_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
uint64_t v_tid_2885_; lean_object* v_traces_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2910_; 
v_tid_2885_ = lean_ctor_get_uint64(v_traceState_2872_, sizeof(void*)*1);
v_traces_2886_ = lean_ctor_get(v_traceState_2872_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_traceState_2872_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2888_ = v_traceState_2872_;
v_isShared_2889_ = v_isSharedCheck_2910_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_traces_2886_);
lean_dec(v_traceState_2872_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2910_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; double v___x_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2893_ = 0;
v___x_2894_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2895_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2895_, 0, v_cls_2858_);
lean_ctor_set(v___x_2895_, 1, v___x_2891_);
lean_ctor_set(v___x_2895_, 2, v___x_2894_);
lean_ctor_set_float(v___x_2895_, sizeof(void*)*3, v___x_2892_);
lean_ctor_set_float(v___x_2895_, sizeof(void*)*3 + 8, v___x_2892_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*3 + 16, v___x_2893_);
v___x_2896_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2897_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v_a_2867_);
lean_ctor_set(v___x_2897_, 2, v___x_2896_);
lean_inc(v_ref_2865_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v_ref_2865_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l_Lean_PersistentArray_push___redArg(v_traces_2886_, v___x_2898_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2899_);
v___x_2901_ = v___x_2888_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2899_);
lean_ctor_set_uint64(v_reuseFailAlloc_2909_, sizeof(void*)*1, v_tid_2885_);
v___x_2901_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2903_; 
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 4, v___x_2901_);
v___x_2903_ = v___x_2883_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_env_2873_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_nextMacroScope_2874_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_ngen_2875_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v_auxDeclNGen_2876_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2908_, 5, v_cache_2877_);
lean_ctor_set(v_reuseFailAlloc_2908_, 6, v_recordedDeps_2878_);
lean_ctor_set(v_reuseFailAlloc_2908_, 7, v_messages_2879_);
lean_ctor_set(v_reuseFailAlloc_2908_, 8, v_infoState_2880_);
lean_ctor_set(v_reuseFailAlloc_2908_, 9, v_snapshotTasks_2881_);
v___x_2903_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_st_ref_put(v___y_2863_, v___x_2903_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2890_);
v___x_2906_ = v___x_2869_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2890_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2913_, lean_object* v_msg_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2913_, v_msg_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2920_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2929_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2930_ = l_Lean_Name_append(v___x_2929_, v___x_2928_);
return v___x_2930_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2933_ = l_Lean_stringToMessageData(v___x_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2936_ = l_Lean_stringToMessageData(v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2939_ = l_Lean_stringToMessageData(v___x_2938_);
return v___x_2939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2943_, lean_object* v_fst_2944_, lean_object* v_fst_2945_, lean_object* v_inst_2946_, lean_object* v_a_2947_, lean_object* v_projInfo_x3f_2948_, lean_object* v_argVars_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2943_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_dummy_2958_; lean_object* v_nargs_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; size_t v_sz_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v_dummy_2958_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2959_ = l_Lean_Expr_getAppNumArgs(v_a_2943_);
lean_inc(v_nargs_2959_);
v___x_2960_ = lean_mk_array(v_nargs_2959_, v_dummy_2958_);
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = lean_nat_sub(v_nargs_2959_, v___x_2961_);
lean_dec(v_nargs_2959_);
lean_inc_ref(v_a_2943_);
v___x_2963_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2943_, v___x_2960_, v___x_2962_);
v___x_2964_ = lean_array_get_size(v___x_2963_);
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___x_2964_);
v_sz_2967_ = lean_array_size(v___x_2963_);
v___x_2968_ = ((size_t)0ULL);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2957_, v_fst_2944_, v_argVars_2949_, v___x_2963_, v_sz_2967_, v___x_2968_, v___x_2966_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec_ref(v___x_2963_);
lean_dec(v_a_2957_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2971_ = lean_array_get_size(v_fst_2944_);
v___x_2972_ = l_List_range(v___x_2971_);
v___x_2973_ = lean_box(0);
v___x_2974_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2945_, v___x_2972_, v___x_2973_);
v___x_2975_ = lean_array_mk(v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2970_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
lean_inc_ref(v_inst_2946_);
lean_inc_ref(v_argVars_2949_);
v___x_2977_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2944_, v_argVars_2949_, v_inst_2946_, v_a_2947_, v_projInfo_x3f_2948_, v___x_2976_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3070_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_3070_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3070_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v_fst_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3068_; 
v_fst_2982_ = lean_ctor_get(v_a_2978_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_a_2978_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_a_2978_, 1);
lean_dec(v_unused_3069_);
v___x_2984_ = v_a_2978_;
v_isShared_2985_ = v_isSharedCheck_3068_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_fst_2982_);
lean_dec(v_a_2978_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3068_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3049_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2953_);
v___x_3050_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_3051_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3049_, v___x_3050_);
lean_dec_ref(v___x_3049_);
if (v___x_3051_ == 0)
{
lean_dec_ref(v_a_2943_);
v___y_2987_ = v___y_2951_;
v___y_2988_ = v___y_2952_;
v___y_2989_ = v___y_2953_;
v___y_2990_ = v___y_2954_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3052_; lean_object* v_a_3053_; uint8_t v___x_3054_; 
v___x_3052_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2943_, v___y_2952_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v___x_3054_ = l_Lean_Expr_hasExprMVar(v_a_3053_);
if (v___x_3054_ == 0)
{
lean_dec(v_a_3053_);
v___y_2987_ = v___y_2951_;
v___y_2988_ = v___y_2952_;
v___y_2989_ = v___y_2953_;
v___y_2990_ = v___y_2954_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_2984_);
lean_dec(v_fst_2982_);
lean_del_object(v___x_2980_);
lean_dec_ref(v_argVars_2949_);
lean_dec_ref(v_inst_2946_);
v___x_3055_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_3056_ = l_Lean_Expr_setPPExplicit(v_a_3053_, v___x_3051_);
v___x_3057_ = l_Lean_indentExpr(v___x_3056_);
v___x_3058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3055_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3058_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
v___jp_2986_:
{
lean_object* v_toCold_2991_; lean_object* v_options_2992_; uint8_t v_hasTrace_2993_; 
v_toCold_2991_ = lean_ctor_get(v___y_2989_, 0);
v_options_2992_ = lean_ctor_get(v_toCold_2991_, 2);
v_hasTrace_2993_ = lean_ctor_get_uint8(v_options_2992_, sizeof(void*)*1);
if (v_hasTrace_2993_ == 0)
{
lean_object* v___x_2995_; 
lean_del_object(v___x_2984_);
lean_dec_ref(v_argVars_2949_);
lean_dec_ref(v_inst_2946_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v_fst_2982_);
v___x_2995_ = v___x_2980_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_fst_2982_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v_inheritedTraceOptions_2997_ = lean_ctor_get(v_toCold_2991_, 11);
v___x_2998_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2999_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_3000_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2997_, v_options_2992_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3002_; 
lean_del_object(v___x_2984_);
lean_dec_ref(v_argVars_2949_);
lean_dec_ref(v_inst_2946_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v_fst_2982_);
v___x_3002_ = v___x_2980_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_fst_2982_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
else
{
size_t v_sz_3004_; lean_object* v___x_3005_; 
lean_del_object(v___x_2980_);
v_sz_3004_ = lean_array_size(v_fst_2982_);
lean_inc(v_fst_2982_);
v___x_3005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2949_, v_sz_3004_, v___x_2968_, v_fst_2982_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec_ref(v_argVars_2949_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_3008_ = l_Lean_MessageData_ofExpr(v_inst_2946_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 7);
lean_ctor_set(v___x_2984_, 1, v___x_3008_);
lean_ctor_set(v___x_2984_, 0, v___x_3007_);
v___x_3010_ = v___x_2984_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3011_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
lean_inc(v_fst_2982_);
v___x_3013_ = lean_array_to_list(v_fst_2982_);
v___x_3014_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_3013_, v___x_2973_);
v___x_3015_ = l_Lean_MessageData_ofList(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3012_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_array_to_list(v_a_3006_);
v___x_3020_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_3021_ = l_Lean_MessageData_joinSep(v___x_3019_, v___x_3020_);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3018_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2998_, v___x_3022_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v___x_3023_, 0);
lean_dec(v_unused_3031_);
v___x_3025_ = v___x_3023_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_dec(v___x_3023_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v_fst_2982_);
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_fst_2982_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec(v_fst_2982_);
v_a_3032_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3023_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3023_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_del_object(v___x_2984_);
lean_dec(v_fst_2982_);
lean_dec_ref(v_inst_2946_);
v_a_3041_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3005_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3005_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_argVars_2949_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_a_2943_);
v_a_3071_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2977_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2977_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v_argVars_2949_);
lean_dec_ref(v_a_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_fst_2944_);
lean_dec_ref(v_a_2943_);
v_a_3079_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2969_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2969_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2949_);
lean_dec_ref(v_a_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_fst_2944_);
lean_dec_ref(v_a_2943_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_3087_, lean_object* v_fst_3088_, lean_object* v_fst_3089_, lean_object* v_inst_3090_, lean_object* v_a_3091_, lean_object* v_projInfo_x3f_3092_, lean_object* v_argVars_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_3087_, v_fst_3088_, v_fst_3089_, v_inst_3090_, v_a_3091_, v_projInfo_x3f_3092_, v_argVars_3093_, v_x_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec_ref(v_x_3094_);
lean_dec(v_projInfo_x3f_3092_);
lean_dec_ref(v_fst_3089_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(lean_object* v_inst_3101_, lean_object* v_projInfo_x3f_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
lean_inc_ref(v_inst_3101_);
v___x_3108_ = lean_infer_type(v_inst_3101_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc_n(v_a_3109_, 2);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = lean_box(0);
v___x_3111_ = 0;
v___x_3112_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3109_, v___x_3110_, v___x_3111_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v_snd_3114_; lean_object* v_fst_3115_; lean_object* v_fst_3116_; lean_object* v_snd_3117_; lean_object* v___x_3118_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v_snd_3114_ = lean_ctor_get(v_a_3113_, 1);
lean_inc(v_snd_3114_);
v_fst_3115_ = lean_ctor_get(v_a_3113_, 0);
lean_inc(v_fst_3115_);
lean_dec(v_a_3113_);
v_fst_3116_ = lean_ctor_get(v_snd_3114_, 0);
lean_inc(v_fst_3116_);
v_snd_3117_ = lean_ctor_get(v_snd_3114_, 1);
lean_inc(v_snd_3117_);
lean_dec(v_snd_3114_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
v___x_3118_ = lean_whnf(v_snd_3117_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___f_3120_; uint8_t v___x_3121_; lean_object* v___x_3122_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
lean_inc(v_a_3109_);
v___f_3120_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3120_, 0, v_a_3119_);
lean_closure_set(v___f_3120_, 1, v_fst_3115_);
lean_closure_set(v___f_3120_, 2, v_fst_3116_);
lean_closure_set(v___f_3120_, 3, v_inst_3101_);
lean_closure_set(v___f_3120_, 4, v_a_3109_);
lean_closure_set(v___f_3120_, 5, v_projInfo_x3f_3102_);
v___x_3121_ = 0;
v___x_3122_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3109_, v___f_3120_, v___x_3121_, v___x_3121_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
return v___x_3122_;
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_fst_3116_);
lean_dec(v_fst_3115_);
lean_dec(v_a_3109_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v_projInfo_x3f_3102_);
lean_dec_ref(v_inst_3101_);
v_a_3123_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3118_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3118_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_a_3109_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v_projInfo_x3f_3102_);
lean_dec_ref(v_inst_3101_);
v_a_3131_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3112_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3112_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v_projInfo_x3f_3102_);
lean_dec_ref(v_inst_3101_);
v_a_3139_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3108_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3108_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1___boxed(lean_object* v_inst_3147_, lean_object* v_projInfo_x3f_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3147_, v_projInfo_x3f_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_3155_, lean_object* v_projInfo_x3f_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___y_3163_; lean_object* v___x_3180_; uint8_t v_transparency_3181_; uint8_t v___x_3182_; uint8_t v___x_3183_; 
v___x_3180_ = l_Lean_Meta_Context_config(v_a_3157_);
v_transparency_3181_ = lean_ctor_get_uint8(v___x_3180_, 9);
lean_dec_ref(v___x_3180_);
v___x_3182_ = 2;
v___x_3183_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v_keyedConfig_3184_; uint8_t v_trackZetaDelta_3185_; lean_object* v_zetaDeltaSet_3186_; lean_object* v_lctx_3187_; lean_object* v_localInstances_3188_; lean_object* v_defEqCtx_x3f_3189_; lean_object* v_synthPendingDepth_3190_; lean_object* v_customCanUnfoldPredicate_x3f_3191_; uint8_t v_univApprox_3192_; uint8_t v_inTypeClassResolution_3193_; uint8_t v_cacheInferType_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_keyedConfig_3184_ = lean_ctor_get(v_a_3157_, 0);
v_trackZetaDelta_3185_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7);
v_zetaDeltaSet_3186_ = lean_ctor_get(v_a_3157_, 1);
v_lctx_3187_ = lean_ctor_get(v_a_3157_, 2);
v_localInstances_3188_ = lean_ctor_get(v_a_3157_, 3);
v_defEqCtx_x3f_3189_ = lean_ctor_get(v_a_3157_, 4);
v_synthPendingDepth_3190_ = lean_ctor_get(v_a_3157_, 5);
v_customCanUnfoldPredicate_x3f_3191_ = lean_ctor_get(v_a_3157_, 6);
v_univApprox_3192_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3193_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7 + 2);
v_cacheInferType_3194_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3184_);
v___x_3195_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3182_, v_keyedConfig_3184_);
lean_inc(v_customCanUnfoldPredicate_x3f_3191_);
lean_inc(v_synthPendingDepth_3190_);
lean_inc(v_defEqCtx_x3f_3189_);
lean_inc_ref(v_localInstances_3188_);
lean_inc_ref(v_lctx_3187_);
lean_inc(v_zetaDeltaSet_3186_);
v___x_3196_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v_zetaDeltaSet_3186_);
lean_ctor_set(v___x_3196_, 2, v_lctx_3187_);
lean_ctor_set(v___x_3196_, 3, v_localInstances_3188_);
lean_ctor_set(v___x_3196_, 4, v_defEqCtx_x3f_3189_);
lean_ctor_set(v___x_3196_, 5, v_synthPendingDepth_3190_);
lean_ctor_set(v___x_3196_, 6, v_customCanUnfoldPredicate_x3f_3191_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7, v_trackZetaDelta_3185_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7 + 1, v_univApprox_3192_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3193_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*7 + 3, v_cacheInferType_3194_);
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
lean_inc(v_a_3158_);
v___x_3197_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3155_, v_projInfo_x3f_3156_, v___x_3196_, v_a_3158_, v_a_3159_, v_a_3160_);
v___y_3163_ = v___x_3197_;
goto v___jp_3162_;
}
else
{
lean_object* v___x_3198_; 
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
lean_inc(v_a_3158_);
lean_inc_ref(v_a_3157_);
v___x_3198_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3155_, v_projInfo_x3f_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
v___y_3163_ = v___x_3198_;
goto v___jp_3162_;
}
v___jp_3162_:
{
if (lean_obj_tag(v___y_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_a_3164_ = lean_ctor_get(v___y_3163_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___y_3163_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___y_3163_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___y_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
v_a_3172_ = lean_ctor_get(v___y_3163_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___y_3163_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___y_3163_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___y_3163_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3199_, lean_object* v_projInfo_x3f_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3199_, v_projInfo_x3f_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3207_, lean_object* v_a_3208_, lean_object* v___x_3209_, lean_object* v_inst_3210_, lean_object* v_R_3211_, lean_object* v_a_3212_, lean_object* v_b_3213_, lean_object* v_c_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3207_, v_a_3208_, v___x_3209_, v_a_3212_, v_b_3213_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3221_, lean_object* v_a_3222_, lean_object* v___x_3223_, lean_object* v_inst_3224_, lean_object* v_R_3225_, lean_object* v_a_3226_, lean_object* v_b_3227_, lean_object* v_c_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3221_, v_a_3222_, v___x_3223_, v_inst_3224_, v_R_3225_, v_a_3226_, v_b_3227_, v_c_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___x_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_upperBound_3221_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3235_, lean_object* v_msg_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3243_, lean_object* v_msg_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3243_, v_msg_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3251_, lean_object* v_argVars_3252_, lean_object* v_inst_3253_, lean_object* v_a_3254_, lean_object* v_projInfo_x3f_3255_, lean_object* v_inst_3256_, lean_object* v_a_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3251_, v_argVars_3252_, v_inst_3253_, v_a_3254_, v_projInfo_x3f_3255_, v_a_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3264_, lean_object* v_argVars_3265_, lean_object* v_inst_3266_, lean_object* v_a_3267_, lean_object* v_projInfo_x3f_3268_, lean_object* v_inst_3269_, lean_object* v_a_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3264_, v_argVars_3265_, v_inst_3266_, v_a_3267_, v_projInfo_x3f_3268_, v_inst_3269_, v_a_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_projInfo_x3f_3268_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3277_, lean_object* v_k_3278_, uint8_t v_cleanupAnnotations_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___f_3285_; uint8_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___f_3285_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3285_, 0, v_k_3278_);
v___x_3286_ = 0;
v___x_3287_ = lean_box(0);
v___x_3288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3286_, v___x_3287_, v_type_3277_, v___f_3285_, v_cleanupAnnotations_3279_, v___x_3286_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
v_a_3297_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3288_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3288_);
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
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3305_, lean_object* v_k_3306_, lean_object* v_cleanupAnnotations_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3313_; lean_object* v_res_3314_; 
v_cleanupAnnotations_boxed_3313_ = lean_unbox(v_cleanupAnnotations_3307_);
v_res_3314_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3305_, v_k_3306_, v_cleanupAnnotations_boxed_3313_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3315_, lean_object* v_type_3316_, lean_object* v_k_3317_, uint8_t v_cleanupAnnotations_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3316_, v_k_3317_, v_cleanupAnnotations_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3325_, lean_object* v_type_3326_, lean_object* v_k_3327_, lean_object* v_cleanupAnnotations_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3334_; lean_object* v_res_3335_; 
v_cleanupAnnotations_boxed_3334_ = lean_unbox(v_cleanupAnnotations_3328_);
v_res_3335_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3325_, v_type_3326_, v_k_3327_, v_cleanupAnnotations_boxed_3334_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
return v_res_3335_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_3343_, uint8_t v___y_3344_, lean_object* v_x_3345_){
_start:
{
if (lean_obj_tag(v_x_3345_) == 1)
{
lean_object* v_pre_3346_; 
v_pre_3346_ = lean_ctor_get(v_x_3345_, 0);
switch(lean_obj_tag(v_pre_3346_))
{
case 1:
{
lean_object* v_pre_3347_; 
v_pre_3347_ = lean_ctor_get(v_pre_3346_, 0);
switch(lean_obj_tag(v_pre_3347_))
{
case 0:
{
lean_object* v_str_3348_; lean_object* v_str_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_str_3348_ = lean_ctor_get(v_x_3345_, 1);
v_str_3349_ = lean_ctor_get(v_pre_3346_, 1);
v___x_3350_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__0));
v___x_3351_ = lean_string_dec_eq(v_str_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; uint8_t v___x_3353_; 
v___x_3352_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__1));
v___x_3353_ = lean_string_dec_eq(v_str_3349_, v___x_3352_);
if (v___x_3353_ == 0)
{
return v___x_3353_;
}
else
{
lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__2));
v___x_3355_ = lean_string_dec_eq(v_str_3348_, v___x_3354_);
if (v___x_3355_ == 0)
{
return v___x_3355_;
}
else
{
return v_suppressElabErrors_3343_;
}
}
}
else
{
lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__3));
v___x_3357_ = lean_string_dec_eq(v_str_3348_, v___x_3356_);
if (v___x_3357_ == 0)
{
return v___x_3357_;
}
else
{
return v_suppressElabErrors_3343_;
}
}
}
case 1:
{
lean_object* v_pre_3358_; 
v_pre_3358_ = lean_ctor_get(v_pre_3347_, 0);
if (lean_obj_tag(v_pre_3358_) == 0)
{
lean_object* v_str_3359_; lean_object* v_str_3360_; lean_object* v_str_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_str_3359_ = lean_ctor_get(v_x_3345_, 1);
v_str_3360_ = lean_ctor_get(v_pre_3346_, 1);
v_str_3361_ = lean_ctor_get(v_pre_3347_, 1);
v___x_3362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__4));
v___x_3363_ = lean_string_dec_eq(v_str_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__5));
v___x_3365_ = lean_string_dec_eq(v_str_3360_, v___x_3364_);
if (v___x_3365_ == 0)
{
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__6));
v___x_3367_ = lean_string_dec_eq(v_str_3359_, v___x_3366_);
if (v___x_3367_ == 0)
{
return v___x_3367_;
}
else
{
return v_suppressElabErrors_3343_;
}
}
}
}
else
{
return v___y_3344_;
}
}
default: 
{
return v___y_3344_;
}
}
}
case 0:
{
lean_object* v_str_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_str_3368_ = lean_ctor_get(v_x_3345_, 1);
v___x_3369_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3370_ = lean_string_dec_eq(v_str_3368_, v___x_3369_);
if (v___x_3370_ == 0)
{
return v___x_3370_;
}
else
{
return v_suppressElabErrors_3343_;
}
}
default: 
{
return v___y_3344_;
}
}
}
else
{
return v___y_3344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_3371_, lean_object* v___y_3372_, lean_object* v_x_3373_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3374_; uint8_t v___y_10347__boxed_3375_; uint8_t v_res_3376_; lean_object* v_r_3377_; 
v_suppressElabErrors_boxed_3374_ = lean_unbox(v_suppressElabErrors_3371_);
v___y_10347__boxed_3375_ = lean_unbox(v___y_3372_);
v_res_3376_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_3374_, v___y_10347__boxed_3375_, v_x_3373_);
lean_dec(v_x_3373_);
v_r_3377_ = lean_box(v_res_3376_);
return v_r_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(lean_object* v_ref_3378_, lean_object* v_msgData_3379_, uint8_t v_severity_3380_, uint8_t v_isSilent_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
uint8_t v___y_3388_; uint8_t v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v_toCold_3395_; lean_object* v___y_3396_; lean_object* v___y_3425_; lean_object* v___y_3426_; uint8_t v___y_3427_; uint8_t v___y_3428_; uint8_t v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; uint8_t v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; uint8_t v___y_3462_; uint8_t v___y_3463_; uint8_t v___y_3464_; uint8_t v___x_3475_; uint8_t v___y_3477_; uint8_t v___y_3478_; uint8_t v___y_3479_; uint8_t v___y_3481_; uint8_t v___x_3489_; 
v___x_3475_ = 2;
v___x_3489_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3380_, v___x_3475_);
if (v___x_3489_ == 0)
{
v___y_3481_ = v___x_3489_;
goto v___jp_3480_;
}
else
{
uint8_t v___x_3490_; 
lean_inc_ref(v_msgData_3379_);
v___x_3490_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3379_);
v___y_3481_ = v___x_3490_;
goto v___jp_3480_;
}
v___jp_3387_:
{
lean_object* v_currNamespace_3397_; lean_object* v_openDecls_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v_env_3403_; lean_object* v_nextMacroScope_3404_; lean_object* v_ngen_3405_; lean_object* v_auxDeclNGen_3406_; lean_object* v_traceState_3407_; lean_object* v_cache_3408_; lean_object* v_recordedDeps_3409_; lean_object* v_messages_3410_; lean_object* v_infoState_3411_; lean_object* v_snapshotTasks_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3423_; 
v_currNamespace_3397_ = lean_ctor_get(v_toCold_3395_, 4);
v_openDecls_3398_ = lean_ctor_get(v_toCold_3395_, 5);
lean_inc(v_openDecls_3398_);
lean_inc(v_currNamespace_3397_);
v___x_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3399_, 0, v_currNamespace_3397_);
lean_ctor_set(v___x_3399_, 1, v_openDecls_3398_);
v___x_3400_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v___y_3392_);
lean_inc_ref(v___y_3391_);
lean_inc_ref(v___y_3390_);
v___x_3401_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3401_, 0, v___y_3390_);
lean_ctor_set(v___x_3401_, 1, v___y_3394_);
lean_ctor_set(v___x_3401_, 2, v___y_3393_);
lean_ctor_set(v___x_3401_, 3, v___y_3391_);
lean_ctor_set(v___x_3401_, 4, v___x_3400_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*5, v___y_3389_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*5 + 1, v___y_3388_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*5 + 2, v_isSilent_3381_);
v___x_3402_ = lean_st_ref_take(v___y_3396_);
v_env_3403_ = lean_ctor_get(v___x_3402_, 0);
v_nextMacroScope_3404_ = lean_ctor_get(v___x_3402_, 1);
v_ngen_3405_ = lean_ctor_get(v___x_3402_, 2);
v_auxDeclNGen_3406_ = lean_ctor_get(v___x_3402_, 3);
v_traceState_3407_ = lean_ctor_get(v___x_3402_, 4);
v_cache_3408_ = lean_ctor_get(v___x_3402_, 5);
v_recordedDeps_3409_ = lean_ctor_get(v___x_3402_, 6);
v_messages_3410_ = lean_ctor_get(v___x_3402_, 7);
v_infoState_3411_ = lean_ctor_get(v___x_3402_, 8);
v_snapshotTasks_3412_ = lean_ctor_get(v___x_3402_, 9);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3414_ = v___x_3402_;
v_isShared_3415_ = v_isSharedCheck_3423_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_snapshotTasks_3412_);
lean_inc(v_infoState_3411_);
lean_inc(v_messages_3410_);
lean_inc(v_recordedDeps_3409_);
lean_inc(v_cache_3408_);
lean_inc(v_traceState_3407_);
lean_inc(v_auxDeclNGen_3406_);
lean_inc(v_ngen_3405_);
lean_inc(v_nextMacroScope_3404_);
lean_inc(v_env_3403_);
lean_dec(v___x_3402_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3423_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3416_ = lean_box(0);
v___x_3417_ = l_Lean_MessageLog_add(v___x_3401_, v_messages_3410_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 7, v___x_3417_);
v___x_3419_ = v___x_3414_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_env_3403_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_nextMacroScope_3404_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_ngen_3405_);
lean_ctor_set(v_reuseFailAlloc_3422_, 3, v_auxDeclNGen_3406_);
lean_ctor_set(v_reuseFailAlloc_3422_, 4, v_traceState_3407_);
lean_ctor_set(v_reuseFailAlloc_3422_, 5, v_cache_3408_);
lean_ctor_set(v_reuseFailAlloc_3422_, 6, v_recordedDeps_3409_);
lean_ctor_set(v_reuseFailAlloc_3422_, 7, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3422_, 8, v_infoState_3411_);
lean_ctor_set(v_reuseFailAlloc_3422_, 9, v_snapshotTasks_3412_);
v___x_3419_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_st_ref_put(v___y_3396_, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3416_);
return v___x_3421_;
}
}
}
v___jp_3424_:
{
lean_object* v_fileName_3433_; lean_object* v_fileMap_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3450_; 
v_fileName_3433_ = lean_ctor_get(v___y_3431_, 0);
v_fileMap_3434_ = lean_ctor_get(v___y_3431_, 1);
v___x_3435_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3379_);
v___x_3436_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3435_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3439_ = v___x_3436_;
v_isShared_3440_ = v_isSharedCheck_3450_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3450_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_inc_ref_n(v_fileMap_3434_, 2);
v___x_3441_ = l_Lean_FileMap_toPosition(v_fileMap_3434_, v___y_3430_);
lean_dec(v___y_3430_);
v___x_3442_ = l_Lean_FileMap_toPosition(v_fileMap_3434_, v___y_3432_);
lean_dec(v___y_3432_);
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
v___x_3444_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3429_ == 0)
{
lean_del_object(v___x_3439_);
lean_dec_ref(v___y_3425_);
v___y_3388_ = v___y_3427_;
v___y_3389_ = v___y_3428_;
v___y_3390_ = v_fileName_3433_;
v___y_3391_ = v___x_3444_;
v___y_3392_ = v_a_3437_;
v___y_3393_ = v___x_3443_;
v___y_3394_ = v___x_3441_;
v_toCold_3395_ = v___y_3426_;
v___y_3396_ = v___y_3385_;
goto v___jp_3387_;
}
else
{
uint8_t v___x_3445_; 
lean_inc(v_a_3437_);
v___x_3445_ = l_Lean_MessageData_hasTag(v___y_3425_, v_a_3437_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_dec_ref_known(v___x_3443_, 1);
lean_dec_ref(v___x_3441_);
lean_dec(v_a_3437_);
v___x_3446_ = lean_box(0);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3446_);
v___x_3448_ = v___x_3439_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
else
{
lean_del_object(v___x_3439_);
v___y_3388_ = v___y_3427_;
v___y_3389_ = v___y_3428_;
v___y_3390_ = v_fileName_3433_;
v___y_3391_ = v___x_3444_;
v___y_3392_ = v_a_3437_;
v___y_3393_ = v___x_3443_;
v___y_3394_ = v___x_3441_;
v_toCold_3395_ = v___y_3426_;
v___y_3396_ = v___y_3385_;
goto v___jp_3387_;
}
}
}
}
v___jp_3451_:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_Syntax_getTailPos_x3f(v___y_3457_, v___y_3456_);
lean_dec(v___y_3457_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_inc(v___y_3458_);
v___y_3425_ = v___y_3453_;
v___y_3426_ = v___y_3454_;
v___y_3427_ = v___y_3455_;
v___y_3428_ = v___y_3456_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___y_3458_;
v___y_3431_ = v___y_3454_;
v___y_3432_ = v___y_3458_;
goto v___jp_3424_;
}
else
{
lean_object* v_val_3460_; 
v_val_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_val_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___y_3425_ = v___y_3453_;
v___y_3426_ = v___y_3454_;
v___y_3427_ = v___y_3455_;
v___y_3428_ = v___y_3456_;
v___y_3429_ = v___y_3452_;
v___y_3430_ = v___y_3458_;
v___y_3431_ = v___y_3454_;
v___y_3432_ = v_val_3460_;
goto v___jp_3424_;
}
}
v___jp_3461_:
{
lean_object* v_toCold_3465_; lean_object* v_ref_3466_; uint8_t v_suppressElabErrors_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___f_3470_; lean_object* v_ref_3471_; lean_object* v___x_3472_; 
v_toCold_3465_ = lean_ctor_get(v___y_3384_, 0);
v_ref_3466_ = lean_ctor_get(v___y_3384_, 2);
v_suppressElabErrors_3467_ = lean_ctor_get_uint8(v___y_3384_, sizeof(void*)*3 + 2);
v___x_3468_ = lean_box(v_suppressElabErrors_3467_);
v___x_3469_ = lean_box(v___y_3462_);
v___f_3470_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3470_, 0, v___x_3468_);
lean_closure_set(v___f_3470_, 1, v___x_3469_);
v_ref_3471_ = l_Lean_replaceRef(v_ref_3378_, v_ref_3466_);
v___x_3472_ = l_Lean_Syntax_getPos_x3f(v_ref_3471_, v___y_3463_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_unsigned_to_nat(0u);
v___y_3452_ = v_suppressElabErrors_3467_;
v___y_3453_ = v___f_3470_;
v___y_3454_ = v_toCold_3465_;
v___y_3455_ = v___y_3464_;
v___y_3456_ = v___y_3463_;
v___y_3457_ = v_ref_3471_;
v___y_3458_ = v___x_3473_;
goto v___jp_3451_;
}
else
{
lean_object* v_val_3474_; 
v_val_3474_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v___x_3472_, 1);
v___y_3452_ = v_suppressElabErrors_3467_;
v___y_3453_ = v___f_3470_;
v___y_3454_ = v_toCold_3465_;
v___y_3455_ = v___y_3464_;
v___y_3456_ = v___y_3463_;
v___y_3457_ = v_ref_3471_;
v___y_3458_ = v_val_3474_;
goto v___jp_3451_;
}
}
v___jp_3476_:
{
if (v___y_3479_ == 0)
{
v___y_3462_ = v___y_3477_;
v___y_3463_ = v___y_3478_;
v___y_3464_ = v_severity_3380_;
goto v___jp_3461_;
}
else
{
v___y_3462_ = v___y_3477_;
v___y_3463_ = v___y_3478_;
v___y_3464_ = v___x_3475_;
goto v___jp_3461_;
}
}
v___jp_3480_:
{
if (v___y_3481_ == 0)
{
uint8_t v___x_3482_; uint8_t v___x_3483_; 
v___x_3482_ = 1;
v___x_3483_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3380_, v___x_3482_);
if (v___x_3483_ == 0)
{
v___y_3477_ = v___y_3481_;
v___y_3478_ = v___y_3481_;
v___y_3479_ = v___x_3483_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3484_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3384_);
v___x_3485_ = l_Lean_warningAsError;
v___x_3486_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3484_, v___x_3485_);
lean_dec_ref(v___x_3484_);
v___y_3477_ = v___y_3481_;
v___y_3478_ = v___y_3481_;
v___y_3479_ = v___x_3486_;
goto v___jp_3476_;
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v_msgData_3379_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_3491_, lean_object* v_msgData_3492_, lean_object* v_severity_3493_, lean_object* v_isSilent_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
uint8_t v_severity_boxed_3500_; uint8_t v_isSilent_boxed_3501_; lean_object* v_res_3502_; 
v_severity_boxed_3500_ = lean_unbox(v_severity_3493_);
v_isSilent_boxed_3501_ = lean_unbox(v_isSilent_3494_);
v_res_3502_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(v_ref_3491_, v_msgData_3492_, v_severity_boxed_3500_, v_isSilent_boxed_3501_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v_ref_3491_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object* v_msgData_3503_, uint8_t v_severity_3504_, uint8_t v_isSilent_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_ref_3511_; lean_object* v___x_3512_; 
v_ref_3511_ = lean_ctor_get(v___y_3508_, 2);
v___x_3512_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(v_ref_3511_, v_msgData_3503_, v_severity_3504_, v_isSilent_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object* v_msgData_3513_, lean_object* v_severity_3514_, lean_object* v_isSilent_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v_severity_boxed_3521_; uint8_t v_isSilent_boxed_3522_; lean_object* v_res_3523_; 
v_severity_boxed_3521_ = lean_unbox(v_severity_3514_);
v_isSilent_boxed_3522_ = lean_unbox(v_isSilent_3515_);
v_res_3523_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_msgData_3513_, v_severity_boxed_3521_, v_isSilent_boxed_3522_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_msgData_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
uint8_t v___x_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = 1;
v___x_3531_ = 0;
v___x_3532_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_msgData_3524_, v___x_3530_, v___x_3531_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_msgData_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_msgData_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(lean_object* v_as_3540_, size_t v_sz_3541_, size_t v_i_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_a_3550_; uint8_t v___x_3554_; 
v___x_3554_ = lean_usize_dec_lt(v_i_3542_, v_sz_3541_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_b_3543_);
return v___x_3555_;
}
else
{
lean_object* v___x_3556_; lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3556_ = lean_box(0);
v_a_3557_ = lean_array_uget_borrowed(v_as_3540_, v_i_3542_);
v___x_3558_ = l_Lean_Expr_fvarId_x21(v_a_3557_);
lean_inc(v___x_3558_);
v___x_3559_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3558_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; uint8_t v___x_3561_; uint8_t v___x_3562_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = lean_unbox(v_a_3560_);
lean_dec(v_a_3560_);
v___x_3562_ = l_Lean_BinderInfo_isInstImplicit(v___x_3561_);
if (v___x_3562_ == 0)
{
lean_dec(v___x_3558_);
v_a_3550_ = v___x_3556_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_st_ref_take(v___y_3544_);
v___x_3564_ = l_Lean_CollectFVars_State_add(v___x_3563_, v___x_3558_);
v___x_3565_ = lean_st_ref_put(v___y_3544_, v___x_3564_);
v_a_3550_ = v___x_3556_;
goto v___jp_3549_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v___x_3558_);
v_a_3566_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3559_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3559_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
v___jp_3549_:
{
size_t v___x_3551_; size_t v___x_3552_; 
v___x_3551_ = ((size_t)1ULL);
v___x_3552_ = lean_usize_add(v_i_3542_, v___x_3551_);
v_i_3542_ = v___x_3552_;
v_b_3543_ = v_a_3550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg___boxed(lean_object* v_as_3574_, lean_object* v_sz_3575_, lean_object* v_i_3576_, lean_object* v_b_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
size_t v_sz_boxed_3583_; size_t v_i_boxed_3584_; lean_object* v_res_3585_; 
v_sz_boxed_3583_ = lean_unbox_usize(v_sz_3575_);
lean_dec(v_sz_3575_);
v_i_boxed_3584_ = lean_unbox_usize(v_i_3576_);
lean_dec(v_i_3576_);
v_res_3585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_as_3574_, v_sz_boxed_3583_, v_i_boxed_3584_, v_b_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v_as_3574_);
return v_res_3585_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object* v_k_3586_, lean_object* v_t_3587_){
_start:
{
if (lean_obj_tag(v_t_3587_) == 0)
{
lean_object* v_k_3588_; lean_object* v_l_3589_; lean_object* v_r_3590_; uint8_t v___x_3591_; 
v_k_3588_ = lean_ctor_get(v_t_3587_, 1);
v_l_3589_ = lean_ctor_get(v_t_3587_, 3);
v_r_3590_ = lean_ctor_get(v_t_3587_, 4);
v___x_3591_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3586_, v_k_3588_);
switch(v___x_3591_)
{
case 0:
{
v_t_3587_ = v_l_3589_;
goto _start;
}
case 1:
{
uint8_t v___x_3593_; 
v___x_3593_ = 1;
return v___x_3593_;
}
default: 
{
v_t_3587_ = v_r_3590_;
goto _start;
}
}
}
else
{
uint8_t v___x_3595_; 
v___x_3595_ = 0;
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object* v_k_3596_, lean_object* v_t_3597_){
_start:
{
uint8_t v_res_3598_; lean_object* v_r_3599_; 
v_res_3598_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_k_3596_, v_t_3597_);
lean_dec(v_t_3597_);
lean_dec(v_k_3596_);
v_r_3599_ = lean_box(v_res_3598_);
return v_r_3599_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__0));
v___x_3602_ = l_Lean_stringToMessageData(v___x_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__2));
v___x_3605_ = l_Lean_stringToMessageData(v___x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_a_3606_, lean_object* v_as_3607_, size_t v_sz_3608_, size_t v_i_3609_, lean_object* v_b_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_a_3616_; uint8_t v___x_3620_; 
v___x_3620_ = lean_usize_dec_lt(v_i_3609_, v_sz_3608_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3621_, 0, v_b_3610_);
return v___x_3621_;
}
else
{
lean_object* v_snd_3622_; 
v_snd_3622_ = lean_ctor_get(v_b_3610_, 1);
lean_inc(v_snd_3622_);
if (lean_obj_tag(v_snd_3622_) == 0)
{
lean_object* v_fst_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3631_; 
v_fst_3623_ = lean_ctor_get(v_b_3610_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_b_3610_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v_b_3610_, 1);
lean_dec(v_unused_3632_);
v___x_3625_ = v_b_3610_;
v_isShared_3626_ = v_isSharedCheck_3631_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_fst_3623_);
lean_dec(v_b_3610_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3631_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_snd_3622_);
v___x_3628_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
return v___x_3629_;
}
}
}
else
{
lean_object* v_fst_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3690_; 
v_fst_3633_ = lean_ctor_get(v_b_3610_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_b_3610_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v_b_3610_, 1);
lean_dec(v_unused_3691_);
v___x_3635_ = v_b_3610_;
v_isShared_3636_ = v_isSharedCheck_3690_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_fst_3633_);
lean_dec(v_b_3610_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3690_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_val_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3689_; 
v_val_3637_ = lean_ctor_get(v_snd_3622_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_snd_3622_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3639_ = v_snd_3622_;
v_isShared_3640_ = v_isSharedCheck_3689_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_val_3637_);
lean_dec(v_snd_3622_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3689_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_fvarSet_3641_; lean_object* v_a_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v_fvarSet_3641_ = lean_ctor_get(v_a_3606_, 1);
v_a_3642_ = lean_array_uget_borrowed(v_as_3607_, v_i_3609_);
v___x_3643_ = lean_unsigned_to_nat(1u);
v___x_3644_ = lean_nat_add(v_val_3637_, v___x_3643_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3644_);
v___x_3646_ = v___x_3639_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = l_Lean_Expr_fvarId_x21(v_a_3642_);
v___x_3648_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v___x_3647_, v_fvarSet_3641_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Lean_FVarId_getDecl___redArg(v___x_3647_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3651_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v___x_3651_ = l_Lean_LocalDecl_ppAsBinder(v_a_3650_);
if (lean_obj_tag(v___x_3651_) == 1)
{
lean_object* v_val_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3673_; 
v_val_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3673_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_val_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3673_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1);
v___x_3657_ = l_Nat_reprFast(v_val_3637_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 3);
lean_ctor_set(v___x_3654_, 0, v___x_3657_);
v___x_3659_ = v___x_3654_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3660_ = l_Lean_MessageData_ofFormat(v___x_3659_);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3656_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v_val_3652_);
v___x_3665_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = l_Lean_indentD(v___x_3666_);
v___x_3668_ = lean_array_push(v_fst_3633_, v___x_3667_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3646_);
lean_ctor_set(v___x_3635_, 0, v___x_3668_);
v___x_3670_ = v___x_3635_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3646_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_a_3616_ = v___x_3670_;
goto v___jp_3615_;
}
}
}
}
else
{
lean_object* v___x_3675_; 
lean_dec(v___x_3651_);
lean_dec(v_val_3637_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3646_);
v___x_3675_ = v___x_3635_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_fst_3633_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3646_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
v_a_3616_ = v___x_3675_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v___x_3646_);
lean_dec(v_val_3637_);
lean_del_object(v___x_3635_);
lean_dec(v_fst_3633_);
v_a_3677_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3649_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3649_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v___x_3686_; 
lean_dec(v___x_3647_);
lean_dec(v_val_3637_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3646_);
v___x_3686_ = v___x_3635_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_fst_3633_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3646_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
v_a_3616_ = v___x_3686_;
goto v___jp_3615_;
}
}
}
}
}
}
}
v___jp_3615_:
{
size_t v___x_3617_; size_t v___x_3618_; 
v___x_3617_ = ((size_t)1ULL);
v___x_3618_ = lean_usize_add(v_i_3609_, v___x_3617_);
v_i_3609_ = v___x_3618_;
v_b_3610_ = v_a_3616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_a_3692_, lean_object* v_as_3693_, lean_object* v_sz_3694_, lean_object* v_i_3695_, lean_object* v_b_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3694_);
lean_dec(v_sz_3694_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3695_);
lean_dec(v_i_3695_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3692_, v_as_3693_, v_sz_boxed_3701_, v_i_boxed_3702_, v_b_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v_as_3693_);
lean_dec_ref(v_a_3692_);
return v_res_3703_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3706_ = l_Lean_stringToMessageData(v___x_3705_);
return v___x_3706_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3709_ = l_Lean_stringToMessageData(v___x_3708_);
return v___x_3709_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_unsigned_to_nat(16u);
v___x_3712_ = lean_mk_array(v___x_3711_, v___x_3710_);
return v___x_3712_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___x_3713_);
return v___x_3715_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v___x_3725_ = l_Lean_stringToMessageData(v___x_3724_);
return v___x_3725_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11));
v___x_3728_ = l_Lean_stringToMessageData(v___x_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_args_3732_, lean_object* v_ty_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___y_3816_; lean_object* v___x_3817_; 
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3758_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3731_);
lean_ctor_set(v___x_3759_, 2, v___x_3758_);
v___x_3760_ = lean_st_mk_ref(v___x_3759_);
v___x_3817_ = l_Lean_Expr_collectFVars(v_ty_3733_, v___x_3760_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v___x_3818_; size_t v_sz_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
lean_dec_ref_known(v___x_3817_, 1);
v___x_3818_ = lean_box(0);
v_sz_3819_ = lean_array_size(v_args_3732_);
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_args_3732_, v_sz_3819_, v___x_3820_, v___x_3818_, v___x_3760_, v___y_3734_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_dec_ref_known(v___x_3821_, 1);
goto v___jp_3761_;
}
else
{
v___y_3816_ = v___x_3821_;
goto v___jp_3815_;
}
}
else
{
v___y_3816_ = v___x_3817_;
goto v___jp_3815_;
}
v___jp_3739_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
lean_inc_ref(v___y_3742_);
v___x_3743_ = l_Lean_stringToMessageData(v___y_3742_);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___y_3740_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_array_to_list(v___y_3741_);
v___x_3748_ = l_Lean_MessageData_nil;
v___x_3749_ = l_Lean_MessageData_joinSep(v___x_3747_, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3746_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = l_Lean_Expr_hasSorry(v___x_3730_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3752_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3754_;
}
else
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_3752_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3755_;
}
}
v___jp_3761_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_st_ref_get(v___x_3760_);
lean_dec(v___x_3760_);
v___x_3763_ = l_Lean_CollectFVars_State_addDependencies(v___x_3762_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; size_t v_sz_3767_; size_t v___x_3768_; lean_object* v___x_3769_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___x_3765_ = lean_unsigned_to_nat(1u);
v___x_3766_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v_sz_3767_ = lean_array_size(v_args_3732_);
v___x_3768_ = ((size_t)0ULL);
v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3764_, v_args_3732_, v_sz_3767_, v___x_3768_, v___x_3766_, v___y_3734_, v___y_3736_, v___y_3737_);
lean_dec(v_a_3764_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3798_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3798_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3798_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v_fst_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3796_; 
v_fst_3774_ = lean_ctor_get(v_a_3770_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_a_3770_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v_a_3770_, 1);
lean_dec(v_unused_3797_);
v___x_3776_ = v_a_3770_;
v_isShared_3777_ = v_isSharedCheck_3796_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_fst_3774_);
lean_dec(v_a_3770_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3796_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = lean_array_get_size(v_fst_3774_);
v___x_3779_ = lean_nat_dec_eq(v___x_3778_, v___x_3756_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_del_object(v___x_3772_);
v___x_3780_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10);
v___x_3781_ = l_Nat_reprFast(v___x_3778_);
v___x_3782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
v___x_3783_ = l_Lean_MessageData_ofFormat(v___x_3782_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set_tag(v___x_3776_, 7);
lean_ctor_set(v___x_3776_, 1, v___x_3783_);
lean_ctor_set(v___x_3776_, 0, v___x_3780_);
v___x_3785_ = v___x_3776_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3786_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_nat_dec_eq(v___x_3778_, v___x_3765_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
v___x_3789_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13));
v___y_3740_ = v___x_3787_;
v___y_3741_ = v_fst_3774_;
v___y_3742_ = v___x_3789_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3790_; 
v___x_3790_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3740_ = v___x_3787_;
v___y_3741_ = v_fst_3774_;
v___y_3742_ = v___x_3790_;
goto v___jp_3739_;
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_del_object(v___x_3776_);
lean_dec(v_fst_3774_);
v___x_3792_ = lean_box(0);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3792_);
v___x_3794_ = v___x_3772_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
v_a_3799_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3769_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3769_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
v_a_3807_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3763_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3763_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
v___jp_3815_:
{
if (lean_obj_tag(v___y_3816_) == 0)
{
lean_dec_ref_known(v___y_3816_, 1);
goto v___jp_3761_;
}
else
{
lean_dec(v___x_3760_);
return v___y_3816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3822_, lean_object* v___x_3823_, lean_object* v_args_3824_, lean_object* v_ty_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3822_, v___x_3823_, v_args_3824_, v_ty_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec_ref(v_args_3824_);
lean_dec_ref(v___x_3822_);
return v_res_3831_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_e_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_Expr_cleanupAnnotations(v_e_3832_);
switch(lean_obj_tag(v___x_3833_))
{
case 7:
{
lean_object* v_body_3834_; uint8_t v_binderInfo_3835_; uint8_t v___x_3836_; 
v_body_3834_ = lean_ctor_get(v___x_3833_, 2);
lean_inc_ref(v_body_3834_);
v_binderInfo_3835_ = lean_ctor_get_uint8(v___x_3833_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3833_, 3);
v___x_3836_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = lean_unsigned_to_nat(0u);
v___x_3838_ = lean_expr_has_loose_bvar(v_body_3834_, v___x_3837_);
if (v___x_3838_ == 0)
{
uint8_t v___x_3839_; 
lean_dec_ref(v_body_3834_);
v___x_3839_ = 1;
return v___x_3839_;
}
else
{
v_e_3832_ = v_body_3834_;
goto _start;
}
}
else
{
v_e_3832_ = v_body_3834_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3842_; 
v_body_3842_ = lean_ctor_get(v___x_3833_, 3);
lean_inc_ref(v_body_3842_);
lean_dec_ref_known(v___x_3833_, 4);
v_e_3832_ = v_body_3842_;
goto _start;
}
default: 
{
uint8_t v___x_3844_; 
lean_dec_ref(v___x_3833_);
v___x_3844_ = 0;
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_e_3845_){
_start:
{
uint8_t v_res_3846_; lean_object* v_r_3847_; 
v_res_3846_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_e_3845_);
v_r_3847_ = lean_box(v_res_3846_);
return v_r_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3854_ = l_Lean_ConstantInfo_type(v_cinfo_3848_);
lean_inc_ref(v___x_3854_);
v___x_3855_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec_ref(v___x_3854_);
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
else
{
lean_object* v___x_3858_; lean_object* v___f_3859_; uint8_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3858_ = lean_box(1);
lean_inc_ref(v___x_3854_);
v___f_3859_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3859_, 0, v___x_3854_);
lean_closure_set(v___f_3859_, 1, v___x_3858_);
v___x_3860_ = 0;
v___x_3861_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3854_, v___f_3859_, v___x_3860_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
return v___x_3861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec_ref(v_cinfo_3862_);
return v_res_3868_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_00_u03b2_3869_, lean_object* v_k_3870_, lean_object* v_t_3871_){
_start:
{
uint8_t v___x_3872_; 
v___x_3872_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_k_3870_, v_t_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_00_u03b2_3873_, lean_object* v_k_3874_, lean_object* v_t_3875_){
_start:
{
uint8_t v_res_3876_; lean_object* v_r_3877_; 
v_res_3876_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_00_u03b2_3873_, v_k_3874_, v_t_3875_);
lean_dec(v_t_3875_);
lean_dec(v_k_3874_);
v_r_3877_ = lean_box(v_res_3876_);
return v_r_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_a_3878_, lean_object* v_as_3879_, size_t v_sz_3880_, size_t v_i_3881_, lean_object* v_b_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3878_, v_as_3879_, v_sz_3880_, v_i_3881_, v_b_3882_, v___y_3883_, v___y_3885_, v___y_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_a_3889_, lean_object* v_as_3890_, lean_object* v_sz_3891_, lean_object* v_i_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
size_t v_sz_boxed_3899_; size_t v_i_boxed_3900_; lean_object* v_res_3901_; 
v_sz_boxed_3899_ = lean_unbox_usize(v_sz_3891_);
lean_dec(v_sz_3891_);
v_i_boxed_3900_ = lean_unbox_usize(v_i_3892_);
lean_dec(v_i_3892_);
v_res_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_a_3889_, v_as_3890_, v_sz_boxed_3899_, v_i_boxed_3900_, v_b_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v_as_3890_);
lean_dec_ref(v_a_3889_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_as_3902_, size_t v_sz_3903_, size_t v_i_3904_, lean_object* v_b_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_as_3902_, v_sz_3903_, v_i_3904_, v_b_3905_, v___y_3906_, v___y_3907_, v___y_3909_, v___y_3910_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_as_3913_, lean_object* v_sz_3914_, lean_object* v_i_3915_, lean_object* v_b_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
size_t v_sz_boxed_3923_; size_t v_i_boxed_3924_; lean_object* v_res_3925_; 
v_sz_boxed_3923_ = lean_unbox_usize(v_sz_3914_);
lean_dec(v_sz_3914_);
v_i_boxed_3924_ = lean_unbox_usize(v_i_3915_);
lean_dec(v_i_3915_);
v_res_3925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_as_3913_, v_sz_boxed_3923_, v_i_boxed_3924_, v_b_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v_as_3913_);
return v_res_3925_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3928_ = l_Lean_stringToMessageData(v___x_3927_);
return v___x_3928_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3934_ = l_Lean_stringToMessageData(v___x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3935_, lean_object* v_x_3936_, lean_object* v_target_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; 
lean_inc_ref(v_target_3937_);
v___x_3943_ = l_Lean_Meta_isClass_x3f(v_target_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3962_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3946_ = v___x_3943_;
v_isShared_3947_ = v_isSharedCheck_3962_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3943_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3962_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
if (lean_obj_tag(v_a_3944_) == 0)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
lean_del_object(v___x_3946_);
v___x_3948_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3949_ = l_Lean_MessageData_ofExpr(v_c_3935_);
v___x_3950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = l_Lean_MessageData_ofExpr(v_target_3937_);
v___x_3954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3952_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3956_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
lean_dec_ref_known(v_a_3944_, 1);
lean_dec_ref(v_target_3937_);
lean_dec_ref(v_c_3935_);
v___x_3958_ = lean_box(0);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 0, v___x_3958_);
v___x_3960_ = v___x_3946_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v_target_3937_);
lean_dec_ref(v_c_3935_);
v_a_3963_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3943_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3943_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3971_, lean_object* v_x_3972_, lean_object* v_target_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3971_, v_x_3972_, v_target_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec_ref(v_x_3972_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v___f_3986_; lean_object* v___x_3987_; 
lean_inc_ref(v_c_3980_);
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3986_, 0, v_c_3980_);
lean_inc(v_a_3984_);
lean_inc_ref(v_a_3983_);
lean_inc(v_a_3982_);
lean_inc_ref(v_a_3981_);
v___x_3987_ = lean_infer_type(v_c_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = 0;
v___x_3990_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3988_, v___f_3986_, v___x_3989_, v___x_3989_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
return v___x_3990_;
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v___f_3986_);
v_a_3991_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3987_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3987_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Meta_checkNonClassInstance(v_c_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___x_4019_; lean_object* v_env_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = lean_st_ref_get(v___y_4017_);
v_env_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc_ref(v_env_4020_);
lean_dec(v___x_4019_);
v___x_4021_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4020_, v_declName_4016_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4023_, v___y_4024_);
lean_dec(v___y_4024_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4027_, v___y_4031_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v_res_4040_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4046_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
lean_ctor_set(v___x_4046_, 2, v___x_4045_);
lean_ctor_set(v___x_4046_, 3, v___x_4045_);
lean_ctor_set(v___x_4046_, 4, v___x_4045_);
lean_ctor_set(v___x_4046_, 5, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_4047_, lean_object* v_b_4048_, uint8_t v_kind_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_toCold_4054_; lean_object* v_currNamespace_4055_; lean_object* v___x_4056_; lean_object* v_env_4057_; lean_object* v_nextMacroScope_4058_; lean_object* v_ngen_4059_; lean_object* v_auxDeclNGen_4060_; lean_object* v_traceState_4061_; lean_object* v_recordedDeps_4062_; lean_object* v_messages_4063_; lean_object* v_infoState_4064_; lean_object* v_snapshotTasks_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4092_; 
v_toCold_4054_ = lean_ctor_get(v___y_4051_, 0);
v_currNamespace_4055_ = lean_ctor_get(v_toCold_4054_, 4);
v___x_4056_ = lean_st_ref_take(v___y_4052_);
v_env_4057_ = lean_ctor_get(v___x_4056_, 0);
v_nextMacroScope_4058_ = lean_ctor_get(v___x_4056_, 1);
v_ngen_4059_ = lean_ctor_get(v___x_4056_, 2);
v_auxDeclNGen_4060_ = lean_ctor_get(v___x_4056_, 3);
v_traceState_4061_ = lean_ctor_get(v___x_4056_, 4);
v_recordedDeps_4062_ = lean_ctor_get(v___x_4056_, 6);
v_messages_4063_ = lean_ctor_get(v___x_4056_, 7);
v_infoState_4064_ = lean_ctor_get(v___x_4056_, 8);
v_snapshotTasks_4065_ = lean_ctor_get(v___x_4056_, 9);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v___x_4056_, 5);
lean_dec(v_unused_4093_);
v___x_4067_ = v___x_4056_;
v_isShared_4068_ = v_isSharedCheck_4092_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_snapshotTasks_4065_);
lean_inc(v_infoState_4064_);
lean_inc(v_messages_4063_);
lean_inc(v_recordedDeps_4062_);
lean_inc(v_traceState_4061_);
lean_inc(v_auxDeclNGen_4060_);
lean_inc(v_ngen_4059_);
lean_inc(v_nextMacroScope_4058_);
lean_inc(v_env_4057_);
lean_dec(v___x_4056_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4092_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
lean_inc(v_currNamespace_4055_);
v___x_4069_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_4057_, v_ext_4047_, v_b_4048_, v_kind_4049_, v_currNamespace_4055_);
v___x_4070_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 5, v___x_4070_);
lean_ctor_set(v___x_4067_, 0, v___x_4069_);
v___x_4072_ = v___x_4067_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_nextMacroScope_4058_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_ngen_4059_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_auxDeclNGen_4060_);
lean_ctor_set(v_reuseFailAlloc_4091_, 4, v_traceState_4061_);
lean_ctor_set(v_reuseFailAlloc_4091_, 5, v___x_4070_);
lean_ctor_set(v_reuseFailAlloc_4091_, 6, v_recordedDeps_4062_);
lean_ctor_set(v_reuseFailAlloc_4091_, 7, v_messages_4063_);
lean_ctor_set(v_reuseFailAlloc_4091_, 8, v_infoState_4064_);
lean_ctor_set(v_reuseFailAlloc_4091_, 9, v_snapshotTasks_4065_);
v___x_4072_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v_mctx_4075_; lean_object* v_zetaDeltaFVarIds_4076_; lean_object* v_postponed_4077_; lean_object* v_diag_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4089_; 
v___x_4073_ = lean_st_ref_put(v___y_4052_, v___x_4072_);
v___x_4074_ = lean_st_ref_take(v___y_4050_);
v_mctx_4075_ = lean_ctor_get(v___x_4074_, 0);
v_zetaDeltaFVarIds_4076_ = lean_ctor_get(v___x_4074_, 2);
v_postponed_4077_ = lean_ctor_get(v___x_4074_, 3);
v_diag_4078_ = lean_ctor_get(v___x_4074_, 4);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v___x_4074_, 1);
lean_dec(v_unused_4090_);
v___x_4080_ = v___x_4074_;
v_isShared_4081_ = v_isSharedCheck_4089_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_diag_4078_);
lean_inc(v_postponed_4077_);
lean_inc(v_zetaDeltaFVarIds_4076_);
lean_inc(v_mctx_4075_);
lean_dec(v___x_4074_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4089_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4082_ = lean_box(0);
v___x_4083_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 1, v___x_4083_);
v___x_4085_ = v___x_4080_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_mctx_4075_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_zetaDeltaFVarIds_4076_);
lean_ctor_set(v_reuseFailAlloc_4088_, 3, v_postponed_4077_);
lean_ctor_set(v_reuseFailAlloc_4088_, 4, v_diag_4078_);
v___x_4085_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_st_ref_put(v___y_4050_, v___x_4085_);
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4082_);
return v___x_4087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_4094_, lean_object* v_b_4095_, lean_object* v_kind_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
uint8_t v_kind_boxed_4101_; lean_object* v_res_4102_; 
v_kind_boxed_4101_ = lean_unbox(v_kind_4096_);
v_res_4102_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4094_, v_b_4095_, v_kind_boxed_4101_, v___y_4097_, v___y_4098_, v___y_4099_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_4103_, lean_object* v_00_u03b2_4104_, lean_object* v_00_u03c3_4105_, lean_object* v_ext_4106_, lean_object* v_b_4107_, uint8_t v_kind_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4106_, v_b_4107_, v_kind_4108_, v___y_4110_, v___y_4111_, v___y_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_4115_, lean_object* v_00_u03b2_4116_, lean_object* v_00_u03c3_4117_, lean_object* v_ext_4118_, lean_object* v_b_4119_, lean_object* v_kind_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v_kind_boxed_4126_; lean_object* v_res_4127_; 
v_kind_boxed_4126_ = lean_unbox(v_kind_4120_);
v_res_4127_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_4115_, v_00_u03b2_4116_, v_00_u03c3_4117_, v_ext_4118_, v_b_4119_, v_kind_boxed_4126_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v___x_4131_; lean_object* v_env_4132_; uint8_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4131_ = lean_st_ref_get(v___y_4129_);
v_env_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc_ref(v_env_4132_);
lean_dec(v___x_4131_);
v___x_4133_ = l_Lean_getReducibilityStatusCore(v_env_4132_, v_declName_4128_);
v___x_4134_ = lean_box(v___x_4133_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4136_, v___y_4137_);
lean_dec(v___y_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4140_, v___y_4144_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4154_, lean_object* v_msg_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_toCold_4161_; lean_object* v_currRecDepth_4162_; lean_object* v_ref_4163_; uint16_t v_optionFlags_4164_; uint8_t v_suppressElabErrors_4165_; uint8_t v_isRecordingDeps_4166_; lean_object* v_ref_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_toCold_4161_ = lean_ctor_get(v___y_4158_, 0);
v_currRecDepth_4162_ = lean_ctor_get(v___y_4158_, 1);
v_ref_4163_ = lean_ctor_get(v___y_4158_, 2);
v_optionFlags_4164_ = lean_ctor_get_uint16(v___y_4158_, sizeof(void*)*3);
v_suppressElabErrors_4165_ = lean_ctor_get_uint8(v___y_4158_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4166_ = lean_ctor_get_uint8(v___y_4158_, sizeof(void*)*3 + 3);
v_ref_4167_ = l_Lean_replaceRef(v_ref_4154_, v_ref_4163_);
lean_inc(v_currRecDepth_4162_);
lean_inc_ref(v_toCold_4161_);
v___x_4168_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4168_, 0, v_toCold_4161_);
lean_ctor_set(v___x_4168_, 1, v_currRecDepth_4162_);
lean_ctor_set(v___x_4168_, 2, v_ref_4167_);
lean_ctor_set_uint16(v___x_4168_, sizeof(void*)*3, v_optionFlags_4164_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*3 + 2, v_suppressElabErrors_4165_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*3 + 3, v_isRecordingDeps_4166_);
v___x_4169_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4155_, v___y_4156_, v___y_4157_, v___x_4168_, v___y_4159_);
lean_dec_ref_known(v___x_4168_, 3);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4170_, lean_object* v_msg_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4170_, v_msg_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v_ref_4170_);
return v_res_4177_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
lean_ctor_set(v___x_4183_, 2, v___x_4182_);
lean_ctor_set(v___x_4183_, 3, v___x_4182_);
lean_ctor_set(v___x_4183_, 4, v___x_4181_);
lean_ctor_set(v___x_4183_, 5, v___x_4181_);
lean_ctor_set(v___x_4183_, 6, v___x_4181_);
lean_ctor_set(v___x_4183_, 7, v___x_4181_);
lean_ctor_set(v___x_4183_, 8, v___x_4181_);
lean_ctor_set(v___x_4183_, 9, v___x_4181_);
lean_ctor_set(v___x_4183_, 10, v___x_4181_);
lean_ctor_set(v___x_4183_, 11, v___x_4180_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = lean_unsigned_to_nat(32u);
v___x_4185_ = lean_mk_empty_array_with_capacity(v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
size_t v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4187_ = ((size_t)5ULL);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = lean_unsigned_to_nat(32u);
v___x_4190_ = lean_mk_empty_array_with_capacity(v___x_4189_);
v___x_4191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4192_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___x_4190_);
lean_ctor_set(v___x_4192_, 2, v___x_4188_);
lean_ctor_set(v___x_4192_, 3, v___x_4188_);
lean_ctor_set_usize(v___x_4192_, 4, v___x_4187_);
return v___x_4192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4193_ = lean_box(1);
v___x_4194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4194_);
lean_ctor_set(v___x_4196_, 2, v___x_4193_);
return v___x_4196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5));
v___x_4199_ = l_Lean_stringToMessageData(v___x_4198_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7));
v___x_4202_ = l_Lean_stringToMessageData(v___x_4201_);
return v___x_4202_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10(void){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9));
v___x_4205_ = l_Lean_stringToMessageData(v___x_4204_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11));
v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13));
v___x_4211_ = l_Lean_stringToMessageData(v___x_4210_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15));
v___x_4214_ = l_Lean_stringToMessageData(v___x_4213_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17));
v___x_4217_ = l_Lean_stringToMessageData(v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4218_, lean_object* v_declHint_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v_env_4224_; uint8_t v___x_4225_; 
v___x_4222_ = lean_box(0);
v___x_4223_ = lean_st_ref_get(v___y_4220_);
v_env_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc_ref(v_env_4224_);
lean_dec(v___x_4223_);
v___x_4225_ = l_Lean_Name_isAnonymous(v_declHint_4219_);
if (v___x_4225_ == 0)
{
uint8_t v_isExporting_4226_; 
v_isExporting_4226_ = lean_ctor_get_uint8(v_env_4224_, sizeof(void*)*13);
if (v_isExporting_4226_ == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref(v_env_4224_);
lean_dec(v_declHint_4219_);
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_msg_4218_);
return v___x_4227_;
}
else
{
lean_object* v___x_4228_; uint8_t v___x_4229_; 
lean_inc_ref(v_env_4224_);
v___x_4228_ = l_Lean_Environment_setExporting(v_env_4224_, v___x_4225_);
lean_inc(v_declHint_4219_);
lean_inc_ref(v___x_4228_);
v___x_4229_ = l_Lean_Environment_contains(v___x_4228_, v_declHint_4219_, v_isExporting_4226_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; 
lean_dec_ref(v___x_4228_);
lean_dec_ref(v_env_4224_);
lean_dec(v_declHint_4219_);
v___x_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4230_, 0, v_msg_4218_);
return v___x_4230_;
}
else
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v_c_4236_; lean_object* v___x_4237_; 
v___x_4231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4233_ = l_Lean_Options_empty;
v___x_4234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4228_);
lean_ctor_set(v___x_4234_, 1, v___x_4231_);
lean_ctor_set(v___x_4234_, 2, v___x_4232_);
lean_ctor_set(v___x_4234_, 3, v___x_4233_);
lean_inc(v_declHint_4219_);
v___x_4235_ = l_Lean_MessageData_ofConstName(v_declHint_4219_, v___x_4225_);
v_c_4236_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4236_, 0, v___x_4234_);
lean_ctor_set(v_c_4236_, 1, v___x_4235_);
v___x_4237_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4224_, v_declHint_4219_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
lean_dec_ref(v_env_4224_);
lean_dec(v_declHint_4219_);
v___x_4238_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6);
v___x_4239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
lean_ctor_set(v___x_4239_, 1, v_c_4236_);
v___x_4240_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4239_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = l_Lean_MessageData_note(v___x_4241_);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v_msg_4218_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
return v___x_4244_;
}
else
{
lean_object* v_val_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4279_; 
v_val_4245_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4247_ = v___x_4237_;
v_isShared_4248_ = v_isSharedCheck_4279_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_val_4245_);
lean_dec(v___x_4237_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4279_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v_mod_4251_; uint8_t v___x_4252_; 
v___x_4249_ = l_Lean_Environment_header(v_env_4224_);
lean_dec_ref(v_env_4224_);
v___x_4250_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4249_);
v_mod_4251_ = lean_array_get(v___x_4222_, v___x_4250_, v_val_4245_);
lean_dec(v_val_4245_);
lean_dec_ref(v___x_4250_);
v___x_4252_ = l_Lean_isPrivateName(v_declHint_4219_);
lean_dec(v_declHint_4219_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4264_; 
v___x_4253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
lean_ctor_set(v___x_4254_, 1, v_c_4236_);
v___x_4255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = l_Lean_MessageData_ofName(v_mod_4251_);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_MessageData_note(v___x_4260_);
v___x_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4262_, 0, v_msg_4218_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set_tag(v___x_4247_, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4262_);
v___x_4264_ = v___x_4247_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
else
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4277_; 
v___x_4266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
lean_ctor_set(v___x_4267_, 1, v_c_4236_);
v___x_4268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = l_Lean_MessageData_ofName(v_mod_4251_);
v___x_4271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4269_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18);
v___x_4273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l_Lean_MessageData_note(v___x_4273_);
v___x_4275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4275_, 0, v_msg_4218_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set_tag(v___x_4247_, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4275_);
v___x_4277_ = v___x_4247_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4280_; 
lean_dec_ref(v_env_4224_);
lean_dec(v_declHint_4219_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v_msg_4218_);
return v___x_4280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4281_, lean_object* v_declHint_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4281_, v_declHint_4282_, v___y_4283_);
lean_dec(v___y_4283_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4286_, lean_object* v_declHint_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___x_4293_; lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4303_; 
v___x_4293_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4286_, v_declHint_4287_, v___y_4291_);
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4296_ = v___x_4293_;
v_isShared_4297_ = v_isSharedCheck_4303_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4293_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4303_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4298_ = l_Lean_unknownIdentifierMessageTag;
v___x_4299_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
lean_ctor_set(v___x_4299_, 1, v_a_4294_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4299_);
v___x_4301_ = v___x_4296_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4304_, lean_object* v_declHint_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4304_, v_declHint_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4312_, lean_object* v_msg_4313_, lean_object* v_declHint_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; lean_object* v_a_4321_; lean_object* v___x_4322_; 
v___x_4320_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4313_, v_declHint_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4320_);
v___x_4322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4312_, v_a_4321_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4323_, lean_object* v_msg_4324_, lean_object* v_declHint_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4323_, v_msg_4324_, v_declHint_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v_ref_4323_);
return v_res_4331_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4335_, lean_object* v_constName_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; uint8_t v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4342_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4343_ = 0;
lean_inc(v_constName_4336_);
v___x_4344_ = l_Lean_MessageData_ofConstName(v_constName_4336_, v___x_4343_);
v___x_4345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4342_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4345_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4335_, v___x_4347_, v_constName_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4349_, lean_object* v_constName_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4349_, v_constName_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v_ref_4349_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_ref_4363_; lean_object* v___x_4364_; 
v_ref_4363_ = lean_ctor_get(v___y_4360_, 2);
v___x_4364_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4363_, v_constName_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v_env_4379_; uint8_t v___x_4380_; lean_object* v___x_4381_; 
v___x_4378_ = lean_st_ref_get(v___y_4376_);
v_env_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc_ref(v_env_4379_);
lean_dec(v___x_4378_);
v___x_4380_ = 0;
lean_inc(v_constName_4372_);
v___x_4381_ = l_Lean_Environment_find_x3f(v_env_4379_, v_constName_4372_, v___x_4380_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
return v___x_4382_;
}
else
{
lean_object* v_val_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec(v_constName_4372_);
v_val_4383_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4381_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_val_4383_);
lean_dec(v___x_4381_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set_tag(v___x_4385_, 0);
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_val_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; lean_object* v_env_4405_; uint8_t v___x_4406_; lean_object* v___x_4407_; 
v___x_4404_ = lean_st_ref_get(v___y_4402_);
v_env_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc_ref(v_env_4405_);
lean_dec(v___x_4404_);
v___x_4406_ = 0;
lean_inc(v_constName_4398_);
v___x_4407_ = l_Lean_Environment_findConstVal_x3f(v_env_4405_, v_constName_4398_, v___x_4406_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
return v___x_4408_;
}
else
{
lean_object* v_val_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_constName_4398_);
v_val_4409_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4407_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_val_4409_);
lean_dec(v___x_4407_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 0);
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_val_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
if (lean_obj_tag(v_a_4424_) == 0)
{
lean_object* v___x_4426_; 
v___x_4426_ = l_List_reverse___redArg(v_a_4425_);
return v___x_4426_;
}
else
{
lean_object* v_head_4427_; lean_object* v_tail_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4437_; 
v_head_4427_ = lean_ctor_get(v_a_4424_, 0);
v_tail_4428_ = lean_ctor_get(v_a_4424_, 1);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_a_4424_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4430_ = v_a_4424_;
v_isShared_4431_ = v_isSharedCheck_4437_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_tail_4428_);
lean_inc(v_head_4427_);
lean_dec(v_a_4424_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4437_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = l_Lean_mkLevelParam(v_head_4427_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 1, v_a_4425_);
lean_ctor_set(v___x_4430_, 0, v___x_4432_);
v___x_4434_ = v___x_4430_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_a_4425_);
v___x_4434_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
v_a_4424_ = v_tail_4428_;
v_a_4425_ = v___x_4434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
lean_inc(v_constName_4438_);
v___x_4444_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4456_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4456_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4456_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v_levelParams_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4454_; 
v_levelParams_4449_ = lean_ctor_get(v_a_4445_, 1);
lean_inc(v_levelParams_4449_);
lean_dec(v_a_4445_);
v___x_4450_ = lean_box(0);
v___x_4451_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4449_, v___x_4450_);
v___x_4452_ = l_Lean_mkConst(v_constName_4438_, v___x_4451_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4452_);
v___x_4454_ = v___x_4447_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v_constName_4438_);
v_a_4457_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4444_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4444_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v_res_4471_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4474_ = l_Lean_stringToMessageData(v___x_4473_);
return v___x_4474_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4477_ = l_Lean_stringToMessageData(v___x_4476_);
return v___x_4477_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4480_ = l_Lean_stringToMessageData(v___x_4479_);
return v___x_4480_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4483_ = l_Lean_stringToMessageData(v___x_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4484_, uint8_t v_attrKind_4485_, lean_object* v_prio_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v___x_4492_; 
lean_inc(v_declName_4484_);
v___x_4492_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4484_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___x_4571_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4493_);
lean_dec_ref_known(v___x_4492_, 1);
lean_inc(v_declName_4484_);
v___x_4571_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4484_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref_known(v___x_4571_, 1);
v___x_4573_ = l_Lean_ConstantInfo_type(v_a_4572_);
v___x_4574_ = l_Lean_Expr_hasSorry(v___x_4573_);
lean_dec_ref(v___x_4573_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; 
lean_inc(v_a_4493_);
v___x_4575_ = l_Lean_Meta_checkNonClassInstance(v_a_4493_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v___x_4576_; 
lean_dec_ref_known(v___x_4575_, 1);
v___x_4576_ = l_Lean_Meta_checkImpossibleInstance(v_a_4572_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
lean_dec(v_a_4572_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_dec_ref_known(v___x_4576_, 1);
v___y_4523_ = v_a_4487_;
v___y_4524_ = v_a_4488_;
v___y_4525_ = v_a_4489_;
v___y_4526_ = v_a_4490_;
goto v___jp_4522_;
}
else
{
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
return v___x_4576_;
}
}
else
{
lean_dec(v_a_4572_);
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
return v___x_4575_;
}
}
else
{
lean_dec(v_a_4572_);
v___y_4523_ = v_a_4487_;
v___y_4524_ = v_a_4488_;
v___y_4525_ = v_a_4489_;
v___y_4526_ = v_a_4490_;
goto v___jp_4522_;
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
v_a_4577_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4571_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4571_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
v___jp_4494_:
{
lean_object* v___x_4500_; lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4521_; 
lean_inc(v_declName_4484_);
v___x_4500_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4484_, v___y_4499_);
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4503_ = v___x_4500_;
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4500_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; 
lean_inc(v_a_4493_);
v___x_4505_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4493_, v_a_4501_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4507_; lean_object* v___x_4509_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___x_4505_, 1);
v___x_4507_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4504_ == 0)
{
lean_ctor_set_tag(v___x_4503_, 1);
lean_ctor_set(v___x_4503_, 0, v_declName_4484_);
v___x_4509_ = v___x_4503_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_declName_4484_);
v___x_4509_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4510_, 0, v___y_4495_);
lean_ctor_set(v___x_4510_, 1, v_a_4493_);
lean_ctor_set(v___x_4510_, 2, v_prio_4486_);
lean_ctor_set(v___x_4510_, 3, v___x_4509_);
lean_ctor_set(v___x_4510_, 4, v_a_4506_);
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*5, v_attrKind_4485_);
v___x_4511_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4507_, v___x_4510_, v_attrKind_4485_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4511_;
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_del_object(v___x_4503_);
lean_dec_ref(v___y_4495_);
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
v_a_4513_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4505_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4505_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
v___jp_4522_:
{
lean_object* v___x_4527_; 
lean_inc(v_a_4493_);
v___x_4527_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4493_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; lean_object* v_a_4530_; uint8_t v___x_4531_; uint8_t v___x_4532_; uint8_t v___x_4533_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
lean_inc(v_declName_4484_);
v___x_4529_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4484_, v___y_4526_);
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref(v___x_4529_);
v___x_4531_ = 1;
v___x_4532_ = lean_unbox(v_a_4530_);
lean_dec(v_a_4530_);
v___x_4533_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4532_, v___x_4531_);
if (v___x_4533_ == 0)
{
v___y_4495_ = v_a_4528_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
goto v___jp_4494_;
}
else
{
lean_object* v___x_4534_; 
lean_inc(v_declName_4484_);
v___x_4534_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4484_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; uint8_t v___x_4536_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v___x_4536_ = l_Lean_ConstantInfo_isDefinition(v_a_4535_);
lean_dec(v_a_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; lean_object* v_env_4538_; uint8_t v___x_4539_; 
v___x_4537_ = lean_st_ref_get(v___y_4526_);
v_env_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc_ref(v_env_4538_);
lean_dec(v___x_4537_);
lean_inc(v_declName_4484_);
v___x_4539_ = l_Lean_wasOriginallyDefn(v_env_4538_, v_declName_4484_);
if (v___x_4539_ == 0)
{
v___y_4495_ = v_a_4528_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
goto v___jp_4494_;
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4540_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4484_);
v___x_4541_ = l_Lean_MessageData_ofName(v_declName_4484_);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4542_);
lean_ctor_set(v___x_4544_, 1, v___x_4543_);
v___x_4545_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_4544_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_dec_ref_known(v___x_4545_, 1);
v___y_4495_ = v_a_4528_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
goto v___jp_4494_;
}
else
{
lean_dec(v_a_4528_);
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
return v___x_4545_;
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4546_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4525_);
v___x_4547_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4548_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_4546_, v___x_4547_);
lean_dec_ref(v___x_4546_);
if (v___x_4548_ == 0)
{
v___y_4495_ = v_a_4528_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
goto v___jp_4494_;
}
else
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4549_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4484_);
v___x_4550_ = l_Lean_MessageData_ofName(v_declName_4484_);
v___x_4551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4549_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4551_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_4553_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_dec_ref_known(v___x_4554_, 1);
v___y_4495_ = v_a_4528_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
goto v___jp_4494_;
}
else
{
lean_dec(v_a_4528_);
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
return v___x_4554_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4528_);
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
v_a_4555_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4534_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4534_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4493_);
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
v_a_4563_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4527_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4527_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec(v_prio_4486_);
lean_dec(v_declName_4484_);
v_a_4585_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4492_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4492_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4593_, lean_object* v_attrKind_4594_, lean_object* v_prio_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
uint8_t v_attrKind_boxed_4601_; lean_object* v_res_4602_; 
v_attrKind_boxed_4601_ = lean_unbox(v_attrKind_4594_);
v_res_4602_ = l_Lean_Meta_addInstance(v_declName_4593_, v_attrKind_boxed_4601_, v_prio_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4603_, lean_object* v_constName_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4611_, lean_object* v_constName_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4611_, v_constName_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4619_, lean_object* v_ref_4620_, lean_object* v_constName_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4620_, v_constName_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4628_, lean_object* v_ref_4629_, lean_object* v_constName_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4628_, v_ref_4629_, v_constName_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v_ref_4629_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4637_, lean_object* v_ref_4638_, lean_object* v_msg_4639_, lean_object* v_declHint_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4638_, v_msg_4639_, v_declHint_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4647_, lean_object* v_ref_4648_, lean_object* v_msg_4649_, lean_object* v_declHint_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4647_, v_ref_4648_, v_msg_4649_, v_declHint_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v_ref_4648_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4657_, lean_object* v_declHint_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4657_, v_declHint_4658_, v___y_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4665_, lean_object* v_declHint_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4665_, v_declHint_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4673_, lean_object* v_ref_4674_, lean_object* v_msg_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4674_, v_msg_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4682_, lean_object* v_ref_4683_, lean_object* v_msg_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4682_, v_ref_4683_, v_msg_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v_ref_4683_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4691_, uint8_t v_s_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v___x_4696_; lean_object* v_env_4697_; lean_object* v_nextMacroScope_4698_; lean_object* v_ngen_4699_; lean_object* v_auxDeclNGen_4700_; lean_object* v_traceState_4701_; lean_object* v_recordedDeps_4702_; lean_object* v_messages_4703_; lean_object* v_infoState_4704_; lean_object* v_snapshotTasks_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4734_; 
v___x_4696_ = lean_st_ref_take(v___y_4694_);
v_env_4697_ = lean_ctor_get(v___x_4696_, 0);
v_nextMacroScope_4698_ = lean_ctor_get(v___x_4696_, 1);
v_ngen_4699_ = lean_ctor_get(v___x_4696_, 2);
v_auxDeclNGen_4700_ = lean_ctor_get(v___x_4696_, 3);
v_traceState_4701_ = lean_ctor_get(v___x_4696_, 4);
v_recordedDeps_4702_ = lean_ctor_get(v___x_4696_, 6);
v_messages_4703_ = lean_ctor_get(v___x_4696_, 7);
v_infoState_4704_ = lean_ctor_get(v___x_4696_, 8);
v_snapshotTasks_4705_ = lean_ctor_get(v___x_4696_, 9);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4734_ == 0)
{
lean_object* v_unused_4735_; 
v_unused_4735_ = lean_ctor_get(v___x_4696_, 5);
lean_dec(v_unused_4735_);
v___x_4707_ = v___x_4696_;
v_isShared_4708_ = v_isSharedCheck_4734_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_snapshotTasks_4705_);
lean_inc(v_infoState_4704_);
lean_inc(v_messages_4703_);
lean_inc(v_recordedDeps_4702_);
lean_inc(v_traceState_4701_);
lean_inc(v_auxDeclNGen_4700_);
lean_inc(v_ngen_4699_);
lean_inc(v_nextMacroScope_4698_);
lean_inc(v_env_4697_);
lean_dec(v___x_4696_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4734_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
uint8_t v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4714_; 
v___x_4709_ = 0;
v___x_4710_ = lean_box(0);
v___x_4711_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4697_, v_declName_4691_, v_s_4692_, v___x_4709_, v___x_4710_);
v___x_4712_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 5, v___x_4712_);
lean_ctor_set(v___x_4707_, 0, v___x_4711_);
v___x_4714_ = v___x_4707_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v_nextMacroScope_4698_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_ngen_4699_);
lean_ctor_set(v_reuseFailAlloc_4733_, 3, v_auxDeclNGen_4700_);
lean_ctor_set(v_reuseFailAlloc_4733_, 4, v_traceState_4701_);
lean_ctor_set(v_reuseFailAlloc_4733_, 5, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4733_, 6, v_recordedDeps_4702_);
lean_ctor_set(v_reuseFailAlloc_4733_, 7, v_messages_4703_);
lean_ctor_set(v_reuseFailAlloc_4733_, 8, v_infoState_4704_);
lean_ctor_set(v_reuseFailAlloc_4733_, 9, v_snapshotTasks_4705_);
v___x_4714_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v_mctx_4717_; lean_object* v_zetaDeltaFVarIds_4718_; lean_object* v_postponed_4719_; lean_object* v_diag_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4731_; 
v___x_4715_ = lean_st_ref_put(v___y_4694_, v___x_4714_);
v___x_4716_ = lean_st_ref_take(v___y_4693_);
v_mctx_4717_ = lean_ctor_get(v___x_4716_, 0);
v_zetaDeltaFVarIds_4718_ = lean_ctor_get(v___x_4716_, 2);
v_postponed_4719_ = lean_ctor_get(v___x_4716_, 3);
v_diag_4720_ = lean_ctor_get(v___x_4716_, 4);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4716_, 1);
lean_dec(v_unused_4732_);
v___x_4722_ = v___x_4716_;
v_isShared_4723_ = v_isSharedCheck_4731_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_diag_4720_);
lean_inc(v_postponed_4719_);
lean_inc(v_zetaDeltaFVarIds_4718_);
lean_inc(v_mctx_4717_);
lean_dec(v___x_4716_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4731_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4727_; 
v___x_4724_ = lean_box(0);
v___x_4725_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 1, v___x_4725_);
v___x_4727_ = v___x_4722_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_mctx_4717_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_zetaDeltaFVarIds_4718_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_postponed_4719_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_diag_4720_);
v___x_4727_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_st_ref_put(v___y_4693_, v___x_4727_);
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4724_);
return v___x_4729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4736_, lean_object* v_s_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
uint8_t v_s_boxed_4741_; lean_object* v_res_4742_; 
v_s_boxed_4741_ = lean_unbox(v_s_4737_);
v_res_4742_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4736_, v_s_boxed_4741_, v___y_4738_, v___y_4739_);
lean_dec(v___y_4739_);
lean_dec(v___y_4738_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4743_, uint8_t v_s_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4743_, v_s_4744_, v___y_4746_, v___y_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4751_, lean_object* v_s_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
uint8_t v_s_boxed_4758_; lean_object* v_res_4759_; 
v_s_boxed_4758_ = lean_unbox(v_s_4752_);
v_res_4759_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4751_, v_s_boxed_4758_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4760_, uint8_t v_attrKind_4761_, lean_object* v_prio_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
uint8_t v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4768_ = 4;
lean_inc(v_declName_4760_);
v___x_4769_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4760_, v___x_4768_, v_a_4764_, v_a_4766_);
lean_dec_ref(v___x_4769_);
v___x_4770_ = l_Lean_Meta_addInstance(v_declName_4760_, v_attrKind_4761_, v_prio_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4771_, lean_object* v_attrKind_4772_, lean_object* v_prio_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
uint8_t v_attrKind_boxed_4779_; lean_object* v_res_4780_; 
v_attrKind_boxed_4779_ = lean_unbox(v_attrKind_4772_);
v_res_4780_ = l_Lean_Meta_registerInstance(v_declName_4771_, v_attrKind_boxed_4779_, v_prio_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4781_, lean_object* v_x_4782_){
_start:
{
lean_inc_ref(v_a_4781_);
return v_a_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4783_, lean_object* v_x_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4783_, v_x_4784_);
lean_dec_ref(v_x_4784_);
lean_dec_ref(v_a_4783_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v___x_4790_; lean_object* v_toCold_4791_; lean_object* v_env_4792_; lean_object* v_options_4793_; uint8_t v___x_4794_; lean_object* v_env_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4790_ = lean_st_ref_get(v___y_4788_);
v_toCold_4791_ = lean_ctor_get(v___y_4787_, 0);
v_env_4792_ = lean_ctor_get(v___x_4790_, 0);
lean_inc_ref(v_env_4792_);
lean_dec(v___x_4790_);
v_options_4793_ = lean_ctor_get(v_toCold_4791_, 2);
v___x_4794_ = 0;
v_env_4795_ = l_Lean_Environment_setRecordingDeps(v_env_4792_, v___x_4794_);
v___x_4796_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4797_ = lean_unsigned_to_nat(32u);
v___x_4798_ = lean_mk_empty_array_with_capacity(v___x_4797_);
lean_dec_ref(v___x_4798_);
v___x_4799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
lean_inc_ref(v_options_4793_);
v___x_4800_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4800_, 0, v_env_4795_);
lean_ctor_set(v___x_4800_, 1, v___x_4796_);
lean_ctor_set(v___x_4800_, 2, v___x_4799_);
lean_ctor_set(v___x_4800_, 3, v_options_4793_);
v___x_4801_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
lean_ctor_set(v___x_4801_, 1, v_msgData_4786_);
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_ref_4812_; lean_object* v___x_4813_; lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4822_; 
v_ref_4812_ = lean_ctor_get(v___y_4809_, 2);
v___x_4813_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4808_, v___y_4809_, v___y_4810_);
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4822_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4822_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4820_; 
lean_inc(v_ref_4812_);
v___x_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4818_, 0, v_ref_4812_);
lean_ctor_set(v___x_4818_, 1, v_a_4814_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set_tag(v___x_4816_, 1);
lean_ctor_set(v___x_4816_, 0, v___x_4818_);
v___x_4820_ = v___x_4816_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4823_, v___y_4824_, v___y_4825_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
return v_res_4827_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4828_, lean_object* v_i_4829_, lean_object* v_k_4830_){
_start:
{
lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4831_ = lean_array_get_size(v_keys_4828_);
v___x_4832_ = lean_nat_dec_lt(v_i_4829_, v___x_4831_);
if (v___x_4832_ == 0)
{
lean_dec(v_i_4829_);
return v___x_4832_;
}
else
{
lean_object* v_k_x27_4833_; uint8_t v___x_4834_; 
v_k_x27_4833_ = lean_array_fget_borrowed(v_keys_4828_, v_i_4829_);
v___x_4834_ = lean_name_eq(v_k_4830_, v_k_x27_4833_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4835_ = lean_unsigned_to_nat(1u);
v___x_4836_ = lean_nat_add(v_i_4829_, v___x_4835_);
lean_dec(v_i_4829_);
v_i_4829_ = v___x_4836_;
goto _start;
}
else
{
lean_dec(v_i_4829_);
return v___x_4832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4838_, lean_object* v_i_4839_, lean_object* v_k_4840_){
_start:
{
uint8_t v_res_4841_; lean_object* v_r_4842_; 
v_res_4841_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4838_, v_i_4839_, v_k_4840_);
lean_dec(v_k_4840_);
lean_dec_ref(v_keys_4838_);
v_r_4842_ = lean_box(v_res_4841_);
return v_r_4842_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4843_, size_t v_x_4844_, lean_object* v_x_4845_){
_start:
{
if (lean_obj_tag(v_x_4843_) == 0)
{
lean_object* v_es_4846_; lean_object* v___x_4847_; size_t v___x_4848_; size_t v___x_4849_; lean_object* v_j_4850_; lean_object* v___x_4851_; 
v_es_4846_ = lean_ctor_get(v_x_4843_, 0);
v___x_4847_ = lean_box(2);
v___x_4848_ = ((size_t)31ULL);
v___x_4849_ = lean_usize_land(v_x_4844_, v___x_4848_);
v_j_4850_ = lean_usize_to_nat(v___x_4849_);
v___x_4851_ = lean_array_get_borrowed(v___x_4847_, v_es_4846_, v_j_4850_);
lean_dec(v_j_4850_);
switch(lean_obj_tag(v___x_4851_))
{
case 0:
{
lean_object* v_key_4852_; uint8_t v___x_4853_; 
v_key_4852_ = lean_ctor_get(v___x_4851_, 0);
v___x_4853_ = lean_name_eq(v_x_4845_, v_key_4852_);
return v___x_4853_;
}
case 1:
{
lean_object* v_node_4854_; size_t v___x_4855_; size_t v___x_4856_; 
v_node_4854_ = lean_ctor_get(v___x_4851_, 0);
v___x_4855_ = ((size_t)5ULL);
v___x_4856_ = lean_usize_shift_right(v_x_4844_, v___x_4855_);
v_x_4843_ = v_node_4854_;
v_x_4844_ = v___x_4856_;
goto _start;
}
default: 
{
uint8_t v___x_4858_; 
v___x_4858_ = 0;
return v___x_4858_;
}
}
}
else
{
lean_object* v_ks_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v_ks_4859_ = lean_ctor_get(v_x_4843_, 0);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4859_, v___x_4860_, v_x_4845_);
return v___x_4861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4862_, lean_object* v_x_4863_, lean_object* v_x_4864_){
_start:
{
size_t v_x_2437__boxed_4865_; uint8_t v_res_4866_; lean_object* v_r_4867_; 
v_x_2437__boxed_4865_ = lean_unbox_usize(v_x_4863_);
lean_dec(v_x_4863_);
v_res_4866_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4862_, v_x_2437__boxed_4865_, v_x_4864_);
lean_dec(v_x_4864_);
lean_dec_ref(v_x_4862_);
v_r_4867_ = lean_box(v_res_4866_);
return v_r_4867_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4868_, lean_object* v_x_4869_){
_start:
{
uint64_t v___y_4871_; 
if (lean_obj_tag(v_x_4869_) == 0)
{
uint64_t v___x_4874_; 
v___x_4874_ = 1723ULL;
v___y_4871_ = v___x_4874_;
goto v___jp_4870_;
}
else
{
uint64_t v_hash_4875_; 
v_hash_4875_ = lean_ctor_get_uint64(v_x_4869_, sizeof(void*)*2);
v___y_4871_ = v_hash_4875_;
goto v___jp_4870_;
}
v___jp_4870_:
{
size_t v___x_4872_; uint8_t v___x_4873_; 
v___x_4872_ = lean_uint64_to_usize(v___y_4871_);
v___x_4873_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4868_, v___x_4872_, v_x_4869_);
return v___x_4873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4876_, lean_object* v_x_4877_){
_start:
{
uint8_t v_res_4878_; lean_object* v_r_4879_; 
v_res_4878_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4876_, v_x_4877_);
lean_dec(v_x_4877_);
lean_dec_ref(v_x_4876_);
v_r_4879_ = lean_box(v_res_4878_);
return v_r_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4880_, lean_object* v_declName_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v_instanceNames_4888_; uint8_t v___x_4889_; 
v_instanceNames_4888_ = lean_ctor_get(v_d_4880_, 1);
v___x_4889_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4888_, v_declName_4881_);
if (v___x_4889_ == 0)
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
lean_dec_ref(v_d_4880_);
v___x_4890_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4891_ = l_Lean_MessageData_ofConstName(v_declName_4881_, v___x_4889_);
v___x_4892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4890_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4892_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4894_, v___y_4882_, v___y_4883_);
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4895_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
else
{
goto v___jp_4885_;
}
v___jp_4885_:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4886_ = l_Lean_Meta_Instances_eraseCore(v_d_4880_, v_declName_4881_);
v___x_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
return v___x_4887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4904_, lean_object* v_declName_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4904_, v_declName_4905_, v___y_4906_, v___y_4907_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4910_, lean_object* v_declName_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v___x_4915_; lean_object* v_env_4916_; lean_object* v___x_4917_; lean_object* v_ext_4918_; lean_object* v_toEnvExtension_4919_; lean_object* v_asyncMode_4920_; uint8_t v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4915_ = lean_st_ref_get(v___y_4913_);
v_env_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc_ref(v_env_4916_);
lean_dec(v___x_4915_);
v___x_4917_ = l_Lean_Meta_instanceExtension;
v_ext_4918_ = lean_ctor_get(v___x_4917_, 1);
v_toEnvExtension_4919_ = lean_ctor_get(v_ext_4918_, 0);
v_asyncMode_4920_ = lean_ctor_get(v_toEnvExtension_4919_, 2);
v___x_4921_ = 0;
v___x_4922_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4910_, v___x_4917_, v_env_4916_, v_asyncMode_4920_, v___x_4921_);
v___x_4923_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4922_, v_declName_4911_, v___y_4912_, v___y_4913_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4954_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4926_ = v___x_4923_;
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4923_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___f_4928_; lean_object* v___x_4929_; lean_object* v_env_4930_; lean_object* v_nextMacroScope_4931_; lean_object* v_ngen_4932_; lean_object* v_auxDeclNGen_4933_; lean_object* v_traceState_4934_; lean_object* v_recordedDeps_4935_; lean_object* v_messages_4936_; lean_object* v_infoState_4937_; lean_object* v_snapshotTasks_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4952_; 
v___f_4928_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4928_, 0, v_a_4924_);
v___x_4929_ = lean_st_ref_take(v___y_4913_);
v_env_4930_ = lean_ctor_get(v___x_4929_, 0);
v_nextMacroScope_4931_ = lean_ctor_get(v___x_4929_, 1);
v_ngen_4932_ = lean_ctor_get(v___x_4929_, 2);
v_auxDeclNGen_4933_ = lean_ctor_get(v___x_4929_, 3);
v_traceState_4934_ = lean_ctor_get(v___x_4929_, 4);
v_recordedDeps_4935_ = lean_ctor_get(v___x_4929_, 6);
v_messages_4936_ = lean_ctor_get(v___x_4929_, 7);
v_infoState_4937_ = lean_ctor_get(v___x_4929_, 8);
v_snapshotTasks_4938_ = lean_ctor_get(v___x_4929_, 9);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4952_ == 0)
{
lean_object* v_unused_4953_; 
v_unused_4953_ = lean_ctor_get(v___x_4929_, 5);
lean_dec(v_unused_4953_);
v___x_4940_ = v___x_4929_;
v_isShared_4941_ = v_isSharedCheck_4952_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_snapshotTasks_4938_);
lean_inc(v_infoState_4937_);
lean_inc(v_messages_4936_);
lean_inc(v_recordedDeps_4935_);
lean_inc(v_traceState_4934_);
lean_inc(v_auxDeclNGen_4933_);
lean_inc(v_ngen_4932_);
lean_inc(v_nextMacroScope_4931_);
lean_inc(v_env_4930_);
lean_dec(v___x_4929_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4952_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4942_ = lean_box(0);
v___x_4943_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4917_, v_env_4930_, v___f_4928_);
v___x_4944_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 5, v___x_4944_);
lean_ctor_set(v___x_4940_, 0, v___x_4943_);
v___x_4946_ = v___x_4940_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4943_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4931_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4932_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4933_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v_traceState_4934_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v___x_4944_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_recordedDeps_4935_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_messages_4936_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_infoState_4937_);
lean_ctor_set(v_reuseFailAlloc_4951_, 9, v_snapshotTasks_4938_);
v___x_4946_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4947_ = lean_st_ref_put(v___y_4913_, v___x_4946_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4942_);
v___x_4949_ = v___x_4926_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4942_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
}
else
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4962_; 
v_a_4955_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4957_ = v___x_4923_;
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4923_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4963_, lean_object* v_declName_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4963_, v_declName_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec_ref(v___x_4963_);
return v_res_4968_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4975_; uint64_t v___x_4976_; 
v___x_4975_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4976_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4975_);
return v___x_4976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4977_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4978_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4979_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set_uint64(v___x_4979_, sizeof(void*)*1, v___x_4977_);
return v___x_4979_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
return v___x_4981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4982_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4983_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
lean_ctor_set(v___x_4983_, 2, v___x_4982_);
lean_ctor_set(v___x_4983_, 3, v___x_4982_);
lean_ctor_set(v___x_4983_, 4, v___x_4982_);
lean_ctor_set(v___x_4983_, 5, v___x_4982_);
return v___x_4983_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
lean_ctor_set(v___x_4985_, 2, v___x_4984_);
lean_ctor_set(v___x_4985_, 3, v___x_4984_);
lean_ctor_set(v___x_4985_, 4, v___x_4984_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4986_, lean_object* v___x_4987_, lean_object* v_declName_4988_, lean_object* v_stx_4989_, uint8_t v_attrKind_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = lean_unsigned_to_nat(1u);
v___x_4995_ = l_Lean_Syntax_getArg(v_stx_4989_, v___x_4994_);
v___x_4996_ = l_Lean_getAttrParamOptPrio(v___x_4995_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; uint8_t v___x_4998_; uint8_t v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; size_t v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_4997_);
lean_dec_ref_known(v___x_4996_, 1);
v___x_4998_ = 0;
v___x_4999_ = 1;
v___x_5000_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5001_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5002_ = lean_unsigned_to_nat(32u);
v___x_5003_ = lean_mk_empty_array_with_capacity(v___x_5002_);
v___x_5004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_5005_ = ((size_t)5ULL);
lean_inc_n(v___x_4986_, 6);
v___x_5006_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5006_, 0, v___x_5004_);
lean_ctor_set(v___x_5006_, 1, v___x_5003_);
lean_ctor_set(v___x_5006_, 2, v___x_4986_);
lean_ctor_set(v___x_5006_, 3, v___x_4986_);
lean_ctor_set_usize(v___x_5006_, 4, v___x_5005_);
v___x_5007_ = lean_box(1);
lean_inc_ref(v___x_5006_);
v___x_5008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5001_);
lean_ctor_set(v___x_5008_, 1, v___x_5006_);
lean_ctor_set(v___x_5008_, 2, v___x_5007_);
v___x_5009_ = lean_mk_empty_array_with_capacity(v___x_4986_);
v___x_5010_ = lean_box(0);
lean_inc(v___x_4987_);
v___x_5011_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5011_, 0, v___x_5000_);
lean_ctor_set(v___x_5011_, 1, v___x_4987_);
lean_ctor_set(v___x_5011_, 2, v___x_5008_);
lean_ctor_set(v___x_5011_, 3, v___x_5009_);
lean_ctor_set(v___x_5011_, 4, v___x_5010_);
lean_ctor_set(v___x_5011_, 5, v___x_4986_);
lean_ctor_set(v___x_5011_, 6, v___x_5010_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*7, v___x_4998_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*7 + 1, v___x_4998_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*7 + 2, v___x_4998_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*7 + 3, v___x_4999_);
v___x_5012_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5013_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5013_, 0, v___x_4986_);
lean_ctor_set(v___x_5013_, 1, v___x_4986_);
lean_ctor_set(v___x_5013_, 2, v___x_4986_);
lean_ctor_set(v___x_5013_, 3, v___x_4986_);
lean_ctor_set(v___x_5013_, 4, v___x_5001_);
lean_ctor_set(v___x_5013_, 5, v___x_5001_);
lean_ctor_set(v___x_5013_, 6, v___x_5001_);
lean_ctor_set(v___x_5013_, 7, v___x_5001_);
lean_ctor_set(v___x_5013_, 8, v___x_5001_);
lean_ctor_set(v___x_5013_, 9, v___x_5001_);
lean_ctor_set(v___x_5013_, 10, v___x_5001_);
lean_ctor_set(v___x_5013_, 11, v___x_5012_);
v___x_5014_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5015_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5013_);
lean_ctor_set(v___x_5016_, 1, v___x_5014_);
lean_ctor_set(v___x_5016_, 2, v___x_4987_);
lean_ctor_set(v___x_5016_, 3, v___x_5006_);
lean_ctor_set(v___x_5016_, 4, v___x_5015_);
v___x_5017_ = lean_box(0);
v___x_5018_ = lean_st_mk_ref(v___x_5016_);
v___x_5019_ = l_Lean_Meta_addInstance(v_declName_4988_, v_attrKind_4990_, v_a_4997_, v___x_5011_, v___x_5018_, v___y_4991_, v___y_4992_);
lean_dec_ref_known(v___x_5011_, 7);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5027_; 
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5027_ == 0)
{
lean_object* v_unused_5028_; 
v_unused_5028_ = lean_ctor_get(v___x_5019_, 0);
lean_dec(v_unused_5028_);
v___x_5021_ = v___x_5019_;
v_isShared_5022_ = v_isSharedCheck_5027_;
goto v_resetjp_5020_;
}
else
{
lean_dec(v___x_5019_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5027_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; lean_object* v___x_5025_; 
v___x_5023_ = lean_st_ref_get(v___x_5018_);
lean_dec(v___x_5018_);
lean_dec(v___x_5023_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5017_);
v___x_5025_ = v___x_5021_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5017_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
else
{
lean_dec(v___x_5018_);
return v___x_5019_;
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec(v_declName_4988_);
lean_dec(v___x_4987_);
lean_dec(v___x_4986_);
v_a_5029_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_4996_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_4996_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_5037_, lean_object* v___x_5038_, lean_object* v_declName_5039_, lean_object* v_stx_5040_, lean_object* v_attrKind_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_){
_start:
{
uint8_t v_attrKind_boxed_5045_; lean_object* v_res_5046_; 
v_attrKind_boxed_5045_ = lean_unbox(v_attrKind_5041_);
v_res_5046_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_5037_, v___x_5038_, v_declName_5039_, v_stx_5040_, v_attrKind_boxed_5045_, v___y_5042_, v___y_5043_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v_stx_5040_);
return v_res_5046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___f_5048_; 
v___x_5047_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_5048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_5048_, 0, v___x_5047_);
return v___f_5048_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5115_; lean_object* v___f_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___f_5115_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_5116_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5117_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5117_);
lean_ctor_set(v___x_5118_, 1, v___f_5116_);
lean_ctor_set(v___x_5118_, 2, v___f_5115_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; 
v___x_5120_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5121_ = l_Lean_registerBuiltinAttribute(v___x_5120_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5123_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_5124_, lean_object* v_x_5125_, lean_object* v_x_5126_){
_start:
{
uint8_t v___x_5127_; 
v___x_5127_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5125_, v_x_5126_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_5128_, lean_object* v_x_5129_, lean_object* v_x_5130_){
_start:
{
uint8_t v_res_5131_; lean_object* v_r_5132_; 
v_res_5131_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_5128_, v_x_5129_, v_x_5130_);
lean_dec(v_x_5130_);
lean_dec_ref(v_x_5129_);
v_r_5132_ = lean_box(v_res_5131_);
return v_r_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_5133_, lean_object* v_msg_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___x_5138_; 
v___x_5138_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5134_, v___y_5135_, v___y_5136_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5139_, lean_object* v_msg_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5139_, v_msg_5140_, v___y_5141_, v___y_5142_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
return v_res_5144_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5145_, lean_object* v_x_5146_, size_t v_x_5147_, lean_object* v_x_5148_){
_start:
{
uint8_t v___x_5149_; 
v___x_5149_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5146_, v_x_5147_, v_x_5148_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5150_, lean_object* v_x_5151_, lean_object* v_x_5152_, lean_object* v_x_5153_){
_start:
{
size_t v_x_3088__boxed_5154_; uint8_t v_res_5155_; lean_object* v_r_5156_; 
v_x_3088__boxed_5154_ = lean_unbox_usize(v_x_5152_);
lean_dec(v_x_5152_);
v_res_5155_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5150_, v_x_5151_, v_x_3088__boxed_5154_, v_x_5153_);
lean_dec(v_x_5153_);
lean_dec_ref(v_x_5151_);
v_r_5156_ = lean_box(v_res_5155_);
return v_r_5156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5157_, lean_object* v_keys_5158_, lean_object* v_vals_5159_, lean_object* v_heq_5160_, lean_object* v_i_5161_, lean_object* v_k_5162_){
_start:
{
uint8_t v___x_5163_; 
v___x_5163_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5158_, v_i_5161_, v_k_5162_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5164_, lean_object* v_keys_5165_, lean_object* v_vals_5166_, lean_object* v_heq_5167_, lean_object* v_i_5168_, lean_object* v_k_5169_){
_start:
{
uint8_t v_res_5170_; lean_object* v_r_5171_; 
v_res_5170_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5164_, v_keys_5165_, v_vals_5166_, v_heq_5167_, v_i_5168_, v_k_5169_);
lean_dec(v_k_5169_);
lean_dec_ref(v_vals_5166_);
lean_dec_ref(v_keys_5165_);
v_r_5171_ = lean_box(v_res_5170_);
return v_r_5171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; 
v___x_5174_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5175_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5176_ = l_Lean_addBuiltinDocString(v___x_5174_, v___x_5175_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5179_){
_start:
{
lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v_env_5183_; lean_object* v___x_5184_; lean_object* v_ext_5185_; lean_object* v_toEnvExtension_5186_; lean_object* v_asyncMode_5187_; uint8_t v___x_5188_; lean_object* v___x_5189_; lean_object* v_discrTree_5190_; lean_object* v___x_5191_; 
v___x_5181_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5182_ = lean_st_ref_get(v_a_5179_);
v_env_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc_ref(v_env_5183_);
lean_dec(v___x_5182_);
v___x_5184_ = l_Lean_Meta_instanceExtension;
v_ext_5185_ = lean_ctor_get(v___x_5184_, 1);
v_toEnvExtension_5186_ = lean_ctor_get(v_ext_5185_, 0);
v_asyncMode_5187_ = lean_ctor_get(v_toEnvExtension_5186_, 2);
v___x_5188_ = 1;
v___x_5189_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5181_, v___x_5184_, v_env_5183_, v_asyncMode_5187_, v___x_5188_);
v_discrTree_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc_ref(v_discrTree_5190_);
lean_dec(v___x_5189_);
v___x_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5191_, 0, v_discrTree_5190_);
return v___x_5191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5192_);
lean_dec(v_a_5192_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5196_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5199_, v_a_5200_);
lean_dec(v_a_5200_);
lean_dec_ref(v_a_5199_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5203_){
_start:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v_env_5207_; lean_object* v___x_5208_; lean_object* v_ext_5209_; lean_object* v_toEnvExtension_5210_; lean_object* v_asyncMode_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; lean_object* v_erased_5214_; lean_object* v___x_5215_; 
v___x_5205_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5206_ = lean_st_ref_get(v_a_5203_);
v_env_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc_ref(v_env_5207_);
lean_dec(v___x_5206_);
v___x_5208_ = l_Lean_Meta_instanceExtension;
v_ext_5209_ = lean_ctor_get(v___x_5208_, 1);
v_toEnvExtension_5210_ = lean_ctor_get(v_ext_5209_, 0);
v_asyncMode_5211_ = lean_ctor_get(v_toEnvExtension_5210_, 2);
v___x_5212_ = 1;
v___x_5213_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5205_, v___x_5208_, v_env_5207_, v_asyncMode_5211_, v___x_5212_);
v_erased_5214_ = lean_ctor_get(v___x_5213_, 2);
lean_inc_ref(v_erased_5214_);
lean_dec(v___x_5213_);
v___x_5215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5215_, 0, v_erased_5214_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5216_, lean_object* v_a_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5216_);
lean_dec(v_a_5216_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v___x_5222_; 
v___x_5222_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5220_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_Meta_getErasedInstances(v_a_5223_, v_a_5224_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
return v_res_5226_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5227_, lean_object* v_declName_5228_){
_start:
{
lean_object* v___x_5229_; lean_object* v_ext_5230_; lean_object* v_toEnvExtension_5231_; lean_object* v_asyncMode_5232_; lean_object* v___x_5233_; uint8_t v___x_5234_; lean_object* v___x_5235_; lean_object* v_instanceNames_5236_; uint8_t v___x_5237_; 
v___x_5229_ = l_Lean_Meta_instanceExtension;
v_ext_5230_ = lean_ctor_get(v___x_5229_, 1);
v_toEnvExtension_5231_ = lean_ctor_get(v_ext_5230_, 0);
v_asyncMode_5232_ = lean_ctor_get(v_toEnvExtension_5231_, 2);
v___x_5233_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5234_ = 1;
v___x_5235_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5233_, v___x_5229_, v_env_5227_, v_asyncMode_5232_, v___x_5234_);
v_instanceNames_5236_ = lean_ctor_get(v___x_5235_, 1);
lean_inc_ref(v_instanceNames_5236_);
lean_dec(v___x_5235_);
v___x_5237_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5236_, v_declName_5228_);
lean_dec_ref(v_instanceNames_5236_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5238_, lean_object* v_declName_5239_){
_start:
{
uint8_t v_res_5240_; lean_object* v_r_5241_; 
v_res_5240_ = l_Lean_Meta_isInstanceCore(v_env_5238_, v_declName_5239_);
lean_dec(v_declName_5239_);
v_r_5241_ = lean_box(v_res_5240_);
return v_r_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v___x_5245_; lean_object* v_env_5246_; uint8_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5245_ = lean_st_ref_get(v_a_5243_);
v_env_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc_ref(v_env_5246_);
lean_dec(v___x_5245_);
v___x_5247_ = l_Lean_Meta_isInstanceCore(v_env_5246_, v_declName_5242_);
v___x_5248_ = lean_box(v___x_5247_);
v___x_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5248_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_){
_start:
{
lean_object* v_res_5253_; 
v_res_5253_ = l_Lean_Meta_isInstance___redArg(v_declName_5250_, v_a_5251_);
lean_dec(v_a_5251_);
lean_dec(v_declName_5250_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v___x_5258_; 
v___x_5258_ = l_Lean_Meta_isInstance___redArg(v_declName_5254_, v_a_5256_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_Lean_Meta_isInstance(v_declName_5259_, v_a_5260_, v_a_5261_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_declName_5259_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5264_, lean_object* v_vals_5265_, lean_object* v_i_5266_, lean_object* v_k_5267_){
_start:
{
lean_object* v___x_5268_; uint8_t v___x_5269_; 
v___x_5268_ = lean_array_get_size(v_keys_5264_);
v___x_5269_ = lean_nat_dec_lt(v_i_5266_, v___x_5268_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5270_; 
lean_dec(v_i_5266_);
v___x_5270_ = lean_box(0);
return v___x_5270_;
}
else
{
lean_object* v_k_x27_5271_; uint8_t v___x_5272_; 
v_k_x27_5271_ = lean_array_fget_borrowed(v_keys_5264_, v_i_5266_);
v___x_5272_ = lean_name_eq(v_k_5267_, v_k_x27_5271_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; lean_object* v___x_5274_; 
v___x_5273_ = lean_unsigned_to_nat(1u);
v___x_5274_ = lean_nat_add(v_i_5266_, v___x_5273_);
lean_dec(v_i_5266_);
v_i_5266_ = v___x_5274_;
goto _start;
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5276_ = lean_array_fget_borrowed(v_vals_5265_, v_i_5266_);
lean_dec(v_i_5266_);
lean_inc(v___x_5276_);
v___x_5277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5278_, lean_object* v_vals_5279_, lean_object* v_i_5280_, lean_object* v_k_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5278_, v_vals_5279_, v_i_5280_, v_k_5281_);
lean_dec(v_k_5281_);
lean_dec_ref(v_vals_5279_);
lean_dec_ref(v_keys_5278_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5283_, size_t v_x_5284_, lean_object* v_x_5285_){
_start:
{
if (lean_obj_tag(v_x_5283_) == 0)
{
lean_object* v_es_5286_; lean_object* v___x_5287_; size_t v___x_5288_; size_t v___x_5289_; lean_object* v_j_5290_; lean_object* v___x_5291_; 
v_es_5286_ = lean_ctor_get(v_x_5283_, 0);
v___x_5287_ = lean_box(2);
v___x_5288_ = ((size_t)31ULL);
v___x_5289_ = lean_usize_land(v_x_5284_, v___x_5288_);
v_j_5290_ = lean_usize_to_nat(v___x_5289_);
v___x_5291_ = lean_array_get_borrowed(v___x_5287_, v_es_5286_, v_j_5290_);
lean_dec(v_j_5290_);
switch(lean_obj_tag(v___x_5291_))
{
case 0:
{
lean_object* v_key_5292_; lean_object* v_val_5293_; uint8_t v___x_5294_; 
v_key_5292_ = lean_ctor_get(v___x_5291_, 0);
v_val_5293_ = lean_ctor_get(v___x_5291_, 1);
v___x_5294_ = lean_name_eq(v_x_5285_, v_key_5292_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; 
v___x_5295_ = lean_box(0);
return v___x_5295_;
}
else
{
lean_object* v___x_5296_; 
lean_inc(v_val_5293_);
v___x_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5296_, 0, v_val_5293_);
return v___x_5296_;
}
}
case 1:
{
lean_object* v_node_5297_; size_t v___x_5298_; size_t v___x_5299_; 
v_node_5297_ = lean_ctor_get(v___x_5291_, 0);
v___x_5298_ = ((size_t)5ULL);
v___x_5299_ = lean_usize_shift_right(v_x_5284_, v___x_5298_);
v_x_5283_ = v_node_5297_;
v_x_5284_ = v___x_5299_;
goto _start;
}
default: 
{
lean_object* v___x_5301_; 
v___x_5301_ = lean_box(0);
return v___x_5301_;
}
}
}
else
{
lean_object* v_ks_5302_; lean_object* v_vs_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; 
v_ks_5302_ = lean_ctor_get(v_x_5283_, 0);
v_vs_5303_ = lean_ctor_get(v_x_5283_, 1);
v___x_5304_ = lean_unsigned_to_nat(0u);
v___x_5305_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5302_, v_vs_5303_, v___x_5304_, v_x_5285_);
return v___x_5305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5306_, lean_object* v_x_5307_, lean_object* v_x_5308_){
_start:
{
size_t v_x_481__boxed_5309_; lean_object* v_res_5310_; 
v_x_481__boxed_5309_ = lean_unbox_usize(v_x_5307_);
lean_dec(v_x_5307_);
v_res_5310_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5306_, v_x_481__boxed_5309_, v_x_5308_);
lean_dec(v_x_5308_);
lean_dec_ref(v_x_5306_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5311_, lean_object* v_x_5312_){
_start:
{
uint64_t v___y_5314_; 
if (lean_obj_tag(v_x_5312_) == 0)
{
uint64_t v___x_5317_; 
v___x_5317_ = 1723ULL;
v___y_5314_ = v___x_5317_;
goto v___jp_5313_;
}
else
{
uint64_t v_hash_5318_; 
v_hash_5318_ = lean_ctor_get_uint64(v_x_5312_, sizeof(void*)*2);
v___y_5314_ = v_hash_5318_;
goto v___jp_5313_;
}
v___jp_5313_:
{
size_t v___x_5315_; lean_object* v___x_5316_; 
v___x_5315_ = lean_uint64_to_usize(v___y_5314_);
v___x_5316_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5311_, v___x_5315_, v_x_5312_);
return v___x_5316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5319_, lean_object* v_x_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5319_, v_x_5320_);
lean_dec(v_x_5320_);
lean_dec_ref(v_x_5319_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5322_, lean_object* v_a_5323_){
_start:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v_env_5327_; lean_object* v___x_5328_; lean_object* v_ext_5329_; lean_object* v_toEnvExtension_5330_; lean_object* v_asyncMode_5331_; uint8_t v___x_5332_; lean_object* v___x_5333_; lean_object* v_instanceNames_5334_; lean_object* v___x_5335_; 
v___x_5325_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5326_ = lean_st_ref_get(v_a_5323_);
v_env_5327_ = lean_ctor_get(v___x_5326_, 0);
lean_inc_ref(v_env_5327_);
lean_dec(v___x_5326_);
v___x_5328_ = l_Lean_Meta_instanceExtension;
v_ext_5329_ = lean_ctor_get(v___x_5328_, 1);
v_toEnvExtension_5330_ = lean_ctor_get(v_ext_5329_, 0);
v_asyncMode_5331_ = lean_ctor_get(v_toEnvExtension_5330_, 2);
v___x_5332_ = 1;
v___x_5333_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5325_, v___x_5328_, v_env_5327_, v_asyncMode_5331_, v___x_5332_);
v_instanceNames_5334_ = lean_ctor_get(v___x_5333_, 1);
lean_inc_ref(v_instanceNames_5334_);
lean_dec(v___x_5333_);
v___x_5335_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5334_, v_declName_5322_);
lean_dec_ref(v_instanceNames_5334_);
if (lean_obj_tag(v___x_5335_) == 1)
{
lean_object* v_val_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5345_; 
v_val_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5345_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_val_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5345_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v_priority_5340_; lean_object* v___x_5342_; 
v_priority_5340_ = lean_ctor_get(v_val_5336_, 2);
lean_inc(v_priority_5340_);
lean_dec(v_val_5336_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v_priority_5340_);
v___x_5342_ = v___x_5338_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_priority_5340_);
v___x_5342_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
lean_object* v___x_5343_; 
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5342_);
return v___x_5343_;
}
}
}
else
{
lean_object* v___x_5346_; lean_object* v___x_5347_; 
lean_dec(v___x_5335_);
v___x_5346_ = lean_box(0);
v___x_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5346_);
return v___x_5347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_){
_start:
{
lean_object* v_res_5351_; 
v_res_5351_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5348_, v_a_5349_);
lean_dec(v_a_5349_);
lean_dec(v_declName_5348_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v___x_5356_; 
v___x_5356_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5352_, v_a_5354_);
return v___x_5356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5357_, v_a_5358_, v_a_5359_);
lean_dec(v_a_5359_);
lean_dec_ref(v_a_5358_);
lean_dec(v_declName_5357_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5362_, lean_object* v_x_5363_, lean_object* v_x_5364_){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5363_, v_x_5364_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5366_, lean_object* v_x_5367_, lean_object* v_x_5368_){
_start:
{
lean_object* v_res_5369_; 
v_res_5369_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5366_, v_x_5367_, v_x_5368_);
lean_dec(v_x_5368_);
lean_dec_ref(v_x_5367_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5370_, lean_object* v_x_5371_, size_t v_x_5372_, lean_object* v_x_5373_){
_start:
{
lean_object* v___x_5374_; 
v___x_5374_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5371_, v_x_5372_, v_x_5373_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5375_, lean_object* v_x_5376_, lean_object* v_x_5377_, lean_object* v_x_5378_){
_start:
{
size_t v_x_594__boxed_5379_; lean_object* v_res_5380_; 
v_x_594__boxed_5379_ = lean_unbox_usize(v_x_5377_);
lean_dec(v_x_5377_);
v_res_5380_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5375_, v_x_5376_, v_x_594__boxed_5379_, v_x_5378_);
lean_dec(v_x_5378_);
lean_dec_ref(v_x_5376_);
return v_res_5380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5381_, lean_object* v_keys_5382_, lean_object* v_vals_5383_, lean_object* v_heq_5384_, lean_object* v_i_5385_, lean_object* v_k_5386_){
_start:
{
lean_object* v___x_5387_; 
v___x_5387_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5382_, v_vals_5383_, v_i_5385_, v_k_5386_);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5388_, lean_object* v_keys_5389_, lean_object* v_vals_5390_, lean_object* v_heq_5391_, lean_object* v_i_5392_, lean_object* v_k_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5388_, v_keys_5389_, v_vals_5390_, v_heq_5391_, v_i_5392_, v_k_5393_);
lean_dec(v_k_5393_);
lean_dec_ref(v_vals_5390_);
lean_dec_ref(v_keys_5389_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5395_, lean_object* v_a_5396_){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v_env_5400_; lean_object* v___x_5401_; lean_object* v_ext_5402_; lean_object* v_toEnvExtension_5403_; lean_object* v_asyncMode_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; lean_object* v_instanceNames_5407_; lean_object* v___x_5408_; 
v___x_5398_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5399_ = lean_st_ref_get(v_a_5396_);
v_env_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc_ref(v_env_5400_);
lean_dec(v___x_5399_);
v___x_5401_ = l_Lean_Meta_instanceExtension;
v_ext_5402_ = lean_ctor_get(v___x_5401_, 1);
v_toEnvExtension_5403_ = lean_ctor_get(v_ext_5402_, 0);
v_asyncMode_5404_ = lean_ctor_get(v_toEnvExtension_5403_, 2);
v___x_5405_ = 1;
v___x_5406_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5398_, v___x_5401_, v_env_5400_, v_asyncMode_5404_, v___x_5405_);
v_instanceNames_5407_ = lean_ctor_get(v___x_5406_, 1);
lean_inc_ref(v_instanceNames_5407_);
lean_dec(v___x_5406_);
v___x_5408_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5407_, v_declName_5395_);
lean_dec_ref(v_instanceNames_5407_);
if (lean_obj_tag(v___x_5408_) == 1)
{
lean_object* v_val_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5419_; 
v_val_5409_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5411_ = v___x_5408_;
v_isShared_5412_ = v_isSharedCheck_5419_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_val_5409_);
lean_dec(v___x_5408_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5419_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
uint8_t v_attrKind_5413_; lean_object* v___x_5414_; lean_object* v___x_5416_; 
v_attrKind_5413_ = lean_ctor_get_uint8(v_val_5409_, sizeof(void*)*5);
lean_dec(v_val_5409_);
v___x_5414_ = lean_box(v_attrKind_5413_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v___x_5414_);
v___x_5416_ = v___x_5411_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5414_);
v___x_5416_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5417_; 
v___x_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5417_, 0, v___x_5416_);
return v___x_5417_;
}
}
}
else
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
lean_dec(v___x_5408_);
v___x_5420_ = lean_box(0);
v___x_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5421_, 0, v___x_5420_);
return v___x_5421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5422_, v_a_5423_);
lean_dec(v_a_5423_);
lean_dec(v_declName_5422_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_){
_start:
{
lean_object* v___x_5430_; 
v___x_5430_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5426_, v_a_5428_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5431_, v_a_5432_, v_a_5433_);
lean_dec(v_a_5433_);
lean_dec_ref(v_a_5432_);
lean_dec(v_declName_5431_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5440_, lean_object* v_v_5441_, lean_object* v_t_5442_){
_start:
{
if (lean_obj_tag(v_t_5442_) == 0)
{
lean_object* v_size_5443_; lean_object* v_k_5444_; lean_object* v_v_5445_; lean_object* v_l_5446_; lean_object* v_r_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5728_; 
v_size_5443_ = lean_ctor_get(v_t_5442_, 0);
v_k_5444_ = lean_ctor_get(v_t_5442_, 1);
v_v_5445_ = lean_ctor_get(v_t_5442_, 2);
v_l_5446_ = lean_ctor_get(v_t_5442_, 3);
v_r_5447_ = lean_ctor_get(v_t_5442_, 4);
v_isSharedCheck_5728_ = !lean_is_exclusive(v_t_5442_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5449_ = v_t_5442_;
v_isShared_5450_ = v_isSharedCheck_5728_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_r_5447_);
lean_inc(v_l_5446_);
lean_inc(v_v_5445_);
lean_inc(v_k_5444_);
lean_inc(v_size_5443_);
lean_dec(v_t_5442_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5728_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
uint8_t v___x_5451_; 
v___x_5451_ = lean_nat_dec_lt(v_k_5444_, v_k_5440_);
if (v___x_5451_ == 0)
{
uint8_t v___x_5452_; 
v___x_5452_ = lean_nat_dec_eq(v_k_5444_, v_k_5440_);
if (v___x_5452_ == 0)
{
lean_object* v_impl_5453_; lean_object* v___x_5454_; 
lean_dec(v_size_5443_);
v_impl_5453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5440_, v_v_5441_, v_r_5447_);
v___x_5454_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5446_) == 0)
{
lean_object* v_size_5455_; lean_object* v_size_5456_; lean_object* v_k_5457_; lean_object* v_v_5458_; lean_object* v_l_5459_; lean_object* v_r_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; uint8_t v___x_5463_; 
v_size_5455_ = lean_ctor_get(v_l_5446_, 0);
v_size_5456_ = lean_ctor_get(v_impl_5453_, 0);
v_k_5457_ = lean_ctor_get(v_impl_5453_, 1);
v_v_5458_ = lean_ctor_get(v_impl_5453_, 2);
v_l_5459_ = lean_ctor_get(v_impl_5453_, 3);
lean_inc(v_l_5459_);
v_r_5460_ = lean_ctor_get(v_impl_5453_, 4);
v___x_5461_ = lean_unsigned_to_nat(3u);
v___x_5462_ = lean_nat_mul(v___x_5461_, v_size_5455_);
v___x_5463_ = lean_nat_dec_lt(v___x_5462_, v_size_5456_);
lean_dec(v___x_5462_);
if (v___x_5463_ == 0)
{
lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5467_; 
lean_dec(v_l_5459_);
v___x_5464_ = lean_nat_add(v___x_5454_, v_size_5455_);
v___x_5465_ = lean_nat_add(v___x_5464_, v_size_5456_);
lean_dec(v___x_5464_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_impl_5453_);
lean_ctor_set(v___x_5449_, 0, v___x_5465_);
v___x_5467_ = v___x_5449_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v___x_5465_);
lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5468_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5468_, 3, v_l_5446_);
lean_ctor_set(v_reuseFailAlloc_5468_, 4, v_impl_5453_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
return v___x_5467_;
}
}
else
{
lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5532_; 
lean_inc(v_r_5460_);
lean_inc(v_v_5458_);
lean_inc(v_k_5457_);
lean_inc(v_size_5456_);
v_isSharedCheck_5532_ = !lean_is_exclusive(v_impl_5453_);
if (v_isSharedCheck_5532_ == 0)
{
lean_object* v_unused_5533_; lean_object* v_unused_5534_; lean_object* v_unused_5535_; lean_object* v_unused_5536_; lean_object* v_unused_5537_; 
v_unused_5533_ = lean_ctor_get(v_impl_5453_, 4);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_impl_5453_, 3);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_impl_5453_, 2);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_impl_5453_, 1);
lean_dec(v_unused_5536_);
v_unused_5537_ = lean_ctor_get(v_impl_5453_, 0);
lean_dec(v_unused_5537_);
v___x_5470_ = v_impl_5453_;
v_isShared_5471_ = v_isSharedCheck_5532_;
goto v_resetjp_5469_;
}
else
{
lean_dec(v_impl_5453_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5532_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v_size_5472_; lean_object* v_k_5473_; lean_object* v_v_5474_; lean_object* v_l_5475_; lean_object* v_r_5476_; lean_object* v_size_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; uint8_t v___x_5480_; 
v_size_5472_ = lean_ctor_get(v_l_5459_, 0);
v_k_5473_ = lean_ctor_get(v_l_5459_, 1);
v_v_5474_ = lean_ctor_get(v_l_5459_, 2);
v_l_5475_ = lean_ctor_get(v_l_5459_, 3);
v_r_5476_ = lean_ctor_get(v_l_5459_, 4);
v_size_5477_ = lean_ctor_get(v_r_5460_, 0);
v___x_5478_ = lean_unsigned_to_nat(2u);
v___x_5479_ = lean_nat_mul(v___x_5478_, v_size_5477_);
v___x_5480_ = lean_nat_dec_lt(v_size_5472_, v___x_5479_);
lean_dec(v___x_5479_);
if (v___x_5480_ == 0)
{
lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5508_; 
lean_inc(v_r_5476_);
lean_inc(v_l_5475_);
lean_inc(v_v_5474_);
lean_inc(v_k_5473_);
v_isSharedCheck_5508_ = !lean_is_exclusive(v_l_5459_);
if (v_isSharedCheck_5508_ == 0)
{
lean_object* v_unused_5509_; lean_object* v_unused_5510_; lean_object* v_unused_5511_; lean_object* v_unused_5512_; lean_object* v_unused_5513_; 
v_unused_5509_ = lean_ctor_get(v_l_5459_, 4);
lean_dec(v_unused_5509_);
v_unused_5510_ = lean_ctor_get(v_l_5459_, 3);
lean_dec(v_unused_5510_);
v_unused_5511_ = lean_ctor_get(v_l_5459_, 2);
lean_dec(v_unused_5511_);
v_unused_5512_ = lean_ctor_get(v_l_5459_, 1);
lean_dec(v_unused_5512_);
v_unused_5513_ = lean_ctor_get(v_l_5459_, 0);
lean_dec(v_unused_5513_);
v___x_5482_ = v_l_5459_;
v_isShared_5483_ = v_isSharedCheck_5508_;
goto v_resetjp_5481_;
}
else
{
lean_dec(v_l_5459_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5508_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5498_; 
v___x_5484_ = lean_nat_add(v___x_5454_, v_size_5455_);
v___x_5485_ = lean_nat_add(v___x_5484_, v_size_5456_);
lean_dec(v_size_5456_);
if (lean_obj_tag(v_l_5475_) == 0)
{
lean_object* v_size_5506_; 
v_size_5506_ = lean_ctor_get(v_l_5475_, 0);
lean_inc(v_size_5506_);
v___y_5498_ = v_size_5506_;
goto v___jp_5497_;
}
else
{
lean_object* v___x_5507_; 
v___x_5507_ = lean_unsigned_to_nat(0u);
v___y_5498_ = v___x_5507_;
goto v___jp_5497_;
}
v___jp_5486_:
{
lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5490_ = lean_nat_add(v___y_5487_, v___y_5489_);
lean_dec(v___y_5489_);
lean_dec(v___y_5487_);
if (v_isShared_5483_ == 0)
{
lean_ctor_set(v___x_5482_, 4, v_r_5460_);
lean_ctor_set(v___x_5482_, 3, v_r_5476_);
lean_ctor_set(v___x_5482_, 2, v_v_5458_);
lean_ctor_set(v___x_5482_, 1, v_k_5457_);
lean_ctor_set(v___x_5482_, 0, v___x_5490_);
v___x_5492_ = v___x_5482_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5496_, 1, v_k_5457_);
lean_ctor_set(v_reuseFailAlloc_5496_, 2, v_v_5458_);
lean_ctor_set(v_reuseFailAlloc_5496_, 3, v_r_5476_);
lean_ctor_set(v_reuseFailAlloc_5496_, 4, v_r_5460_);
v___x_5492_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5494_; 
if (v_isShared_5471_ == 0)
{
lean_ctor_set(v___x_5470_, 4, v___x_5492_);
lean_ctor_set(v___x_5470_, 3, v___y_5488_);
lean_ctor_set(v___x_5470_, 2, v_v_5474_);
lean_ctor_set(v___x_5470_, 1, v_k_5473_);
lean_ctor_set(v___x_5470_, 0, v___x_5485_);
v___x_5494_ = v___x_5470_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5485_);
lean_ctor_set(v_reuseFailAlloc_5495_, 1, v_k_5473_);
lean_ctor_set(v_reuseFailAlloc_5495_, 2, v_v_5474_);
lean_ctor_set(v_reuseFailAlloc_5495_, 3, v___y_5488_);
lean_ctor_set(v_reuseFailAlloc_5495_, 4, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
v___jp_5497_:
{
lean_object* v___x_5499_; lean_object* v___x_5501_; 
v___x_5499_ = lean_nat_add(v___x_5484_, v___y_5498_);
lean_dec(v___y_5498_);
lean_dec(v___x_5484_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_l_5475_);
lean_ctor_set(v___x_5449_, 0, v___x_5499_);
v___x_5501_ = v___x_5449_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5505_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5505_, 3, v_l_5446_);
lean_ctor_set(v_reuseFailAlloc_5505_, 4, v_l_5475_);
v___x_5501_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
lean_object* v___x_5502_; 
v___x_5502_ = lean_nat_add(v___x_5454_, v_size_5477_);
if (lean_obj_tag(v_r_5476_) == 0)
{
lean_object* v_size_5503_; 
v_size_5503_ = lean_ctor_get(v_r_5476_, 0);
lean_inc(v_size_5503_);
v___y_5487_ = v___x_5502_;
v___y_5488_ = v___x_5501_;
v___y_5489_ = v_size_5503_;
goto v___jp_5486_;
}
else
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_unsigned_to_nat(0u);
v___y_5487_ = v___x_5502_;
v___y_5488_ = v___x_5501_;
v___y_5489_ = v___x_5504_;
goto v___jp_5486_;
}
}
}
}
}
else
{
lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5518_; 
lean_del_object(v___x_5449_);
v___x_5514_ = lean_nat_add(v___x_5454_, v_size_5455_);
v___x_5515_ = lean_nat_add(v___x_5514_, v_size_5456_);
lean_dec(v_size_5456_);
v___x_5516_ = lean_nat_add(v___x_5514_, v_size_5472_);
lean_dec(v___x_5514_);
lean_inc_ref(v_l_5446_);
if (v_isShared_5471_ == 0)
{
lean_ctor_set(v___x_5470_, 4, v_l_5459_);
lean_ctor_set(v___x_5470_, 3, v_l_5446_);
lean_ctor_set(v___x_5470_, 2, v_v_5445_);
lean_ctor_set(v___x_5470_, 1, v_k_5444_);
lean_ctor_set(v___x_5470_, 0, v___x_5516_);
v___x_5518_ = v___x_5470_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5516_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5531_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5531_, 3, v_l_5446_);
lean_ctor_set(v_reuseFailAlloc_5531_, 4, v_l_5459_);
v___x_5518_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
v_isSharedCheck_5525_ = !lean_is_exclusive(v_l_5446_);
if (v_isSharedCheck_5525_ == 0)
{
lean_object* v_unused_5526_; lean_object* v_unused_5527_; lean_object* v_unused_5528_; lean_object* v_unused_5529_; lean_object* v_unused_5530_; 
v_unused_5526_ = lean_ctor_get(v_l_5446_, 4);
lean_dec(v_unused_5526_);
v_unused_5527_ = lean_ctor_get(v_l_5446_, 3);
lean_dec(v_unused_5527_);
v_unused_5528_ = lean_ctor_get(v_l_5446_, 2);
lean_dec(v_unused_5528_);
v_unused_5529_ = lean_ctor_get(v_l_5446_, 1);
lean_dec(v_unused_5529_);
v_unused_5530_ = lean_ctor_get(v_l_5446_, 0);
lean_dec(v_unused_5530_);
v___x_5520_ = v_l_5446_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_dec(v_l_5446_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 4, v_r_5460_);
lean_ctor_set(v___x_5520_, 3, v___x_5518_);
lean_ctor_set(v___x_5520_, 2, v_v_5458_);
lean_ctor_set(v___x_5520_, 1, v_k_5457_);
lean_ctor_set(v___x_5520_, 0, v___x_5515_);
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5515_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_k_5457_);
lean_ctor_set(v_reuseFailAlloc_5524_, 2, v_v_5458_);
lean_ctor_set(v_reuseFailAlloc_5524_, 3, v___x_5518_);
lean_ctor_set(v_reuseFailAlloc_5524_, 4, v_r_5460_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5538_; 
v_l_5538_ = lean_ctor_get(v_impl_5453_, 3);
lean_inc(v_l_5538_);
if (lean_obj_tag(v_l_5538_) == 0)
{
lean_object* v_r_5539_; lean_object* v_k_5540_; lean_object* v_v_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5564_; 
v_r_5539_ = lean_ctor_get(v_impl_5453_, 4);
v_k_5540_ = lean_ctor_get(v_impl_5453_, 1);
v_v_5541_ = lean_ctor_get(v_impl_5453_, 2);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_impl_5453_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; lean_object* v_unused_5566_; 
v_unused_5565_ = lean_ctor_get(v_impl_5453_, 3);
lean_dec(v_unused_5565_);
v_unused_5566_ = lean_ctor_get(v_impl_5453_, 0);
lean_dec(v_unused_5566_);
v___x_5543_ = v_impl_5453_;
v_isShared_5544_ = v_isSharedCheck_5564_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_r_5539_);
lean_inc(v_v_5541_);
lean_inc(v_k_5540_);
lean_dec(v_impl_5453_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5564_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v_k_5545_; lean_object* v_v_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5560_; 
v_k_5545_ = lean_ctor_get(v_l_5538_, 1);
v_v_5546_ = lean_ctor_get(v_l_5538_, 2);
v_isSharedCheck_5560_ = !lean_is_exclusive(v_l_5538_);
if (v_isSharedCheck_5560_ == 0)
{
lean_object* v_unused_5561_; lean_object* v_unused_5562_; lean_object* v_unused_5563_; 
v_unused_5561_ = lean_ctor_get(v_l_5538_, 4);
lean_dec(v_unused_5561_);
v_unused_5562_ = lean_ctor_get(v_l_5538_, 3);
lean_dec(v_unused_5562_);
v_unused_5563_ = lean_ctor_get(v_l_5538_, 0);
lean_dec(v_unused_5563_);
v___x_5548_ = v_l_5538_;
v_isShared_5549_ = v_isSharedCheck_5560_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_v_5546_);
lean_inc(v_k_5545_);
lean_dec(v_l_5538_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5560_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5550_; lean_object* v___x_5552_; 
v___x_5550_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5539_, 2);
if (v_isShared_5549_ == 0)
{
lean_ctor_set(v___x_5548_, 4, v_r_5539_);
lean_ctor_set(v___x_5548_, 3, v_r_5539_);
lean_ctor_set(v___x_5548_, 2, v_v_5445_);
lean_ctor_set(v___x_5548_, 1, v_k_5444_);
lean_ctor_set(v___x_5548_, 0, v___x_5454_);
v___x_5552_ = v___x_5548_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5559_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5559_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5559_, 3, v_r_5539_);
lean_ctor_set(v_reuseFailAlloc_5559_, 4, v_r_5539_);
v___x_5552_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
lean_object* v___x_5554_; 
lean_inc(v_r_5539_);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 3, v_r_5539_);
lean_ctor_set(v___x_5543_, 0, v___x_5454_);
v___x_5554_ = v___x_5543_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v_k_5540_);
lean_ctor_set(v_reuseFailAlloc_5558_, 2, v_v_5541_);
lean_ctor_set(v_reuseFailAlloc_5558_, 3, v_r_5539_);
lean_ctor_set(v_reuseFailAlloc_5558_, 4, v_r_5539_);
v___x_5554_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5556_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v___x_5554_);
lean_ctor_set(v___x_5449_, 3, v___x_5552_);
lean_ctor_set(v___x_5449_, 2, v_v_5546_);
lean_ctor_set(v___x_5449_, 1, v_k_5545_);
lean_ctor_set(v___x_5449_, 0, v___x_5550_);
v___x_5556_ = v___x_5449_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5550_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v_k_5545_);
lean_ctor_set(v_reuseFailAlloc_5557_, 2, v_v_5546_);
lean_ctor_set(v_reuseFailAlloc_5557_, 3, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5557_, 4, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
}
}
else
{
lean_object* v_r_5567_; 
v_r_5567_ = lean_ctor_get(v_impl_5453_, 4);
lean_inc(v_r_5567_);
if (lean_obj_tag(v_r_5567_) == 0)
{
lean_object* v_k_5568_; lean_object* v_v_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5580_; 
v_k_5568_ = lean_ctor_get(v_impl_5453_, 1);
v_v_5569_ = lean_ctor_get(v_impl_5453_, 2);
v_isSharedCheck_5580_ = !lean_is_exclusive(v_impl_5453_);
if (v_isSharedCheck_5580_ == 0)
{
lean_object* v_unused_5581_; lean_object* v_unused_5582_; lean_object* v_unused_5583_; 
v_unused_5581_ = lean_ctor_get(v_impl_5453_, 4);
lean_dec(v_unused_5581_);
v_unused_5582_ = lean_ctor_get(v_impl_5453_, 3);
lean_dec(v_unused_5582_);
v_unused_5583_ = lean_ctor_get(v_impl_5453_, 0);
lean_dec(v_unused_5583_);
v___x_5571_ = v_impl_5453_;
v_isShared_5572_ = v_isSharedCheck_5580_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_v_5569_);
lean_inc(v_k_5568_);
lean_dec(v_impl_5453_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5580_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5573_ = lean_unsigned_to_nat(3u);
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 4, v_l_5538_);
lean_ctor_set(v___x_5571_, 2, v_v_5445_);
lean_ctor_set(v___x_5571_, 1, v_k_5444_);
lean_ctor_set(v___x_5571_, 0, v___x_5454_);
v___x_5575_ = v___x_5571_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5579_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5579_, 3, v_l_5538_);
lean_ctor_set(v_reuseFailAlloc_5579_, 4, v_l_5538_);
v___x_5575_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_5577_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_r_5567_);
lean_ctor_set(v___x_5449_, 3, v___x_5575_);
lean_ctor_set(v___x_5449_, 2, v_v_5569_);
lean_ctor_set(v___x_5449_, 1, v_k_5568_);
lean_ctor_set(v___x_5449_, 0, v___x_5573_);
v___x_5577_ = v___x_5449_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_k_5568_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_v_5569_);
lean_ctor_set(v_reuseFailAlloc_5578_, 3, v___x_5575_);
lean_ctor_set(v_reuseFailAlloc_5578_, 4, v_r_5567_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
else
{
lean_object* v___x_5584_; lean_object* v___x_5586_; 
v___x_5584_ = lean_unsigned_to_nat(2u);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_impl_5453_);
lean_ctor_set(v___x_5449_, 3, v_r_5567_);
lean_ctor_set(v___x_5449_, 0, v___x_5584_);
v___x_5586_ = v___x_5449_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5584_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5587_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5587_, 3, v_r_5567_);
lean_ctor_set(v_reuseFailAlloc_5587_, 4, v_impl_5453_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
}
}
else
{
lean_object* v___x_5589_; 
lean_dec(v_v_5445_);
lean_dec(v_k_5444_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 2, v_v_5441_);
lean_ctor_set(v___x_5449_, 1, v_k_5440_);
v___x_5589_ = v___x_5449_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_size_5443_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v_k_5440_);
lean_ctor_set(v_reuseFailAlloc_5590_, 2, v_v_5441_);
lean_ctor_set(v_reuseFailAlloc_5590_, 3, v_l_5446_);
lean_ctor_set(v_reuseFailAlloc_5590_, 4, v_r_5447_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
else
{
lean_object* v_impl_5591_; lean_object* v___x_5592_; 
lean_dec(v_size_5443_);
v_impl_5591_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5440_, v_v_5441_, v_l_5446_);
v___x_5592_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5447_) == 0)
{
lean_object* v_size_5593_; lean_object* v_size_5594_; lean_object* v_k_5595_; lean_object* v_v_5596_; lean_object* v_l_5597_; lean_object* v_r_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; uint8_t v___x_5601_; 
v_size_5593_ = lean_ctor_get(v_r_5447_, 0);
v_size_5594_ = lean_ctor_get(v_impl_5591_, 0);
v_k_5595_ = lean_ctor_get(v_impl_5591_, 1);
v_v_5596_ = lean_ctor_get(v_impl_5591_, 2);
v_l_5597_ = lean_ctor_get(v_impl_5591_, 3);
v_r_5598_ = lean_ctor_get(v_impl_5591_, 4);
lean_inc(v_r_5598_);
v___x_5599_ = lean_unsigned_to_nat(3u);
v___x_5600_ = lean_nat_mul(v___x_5599_, v_size_5593_);
v___x_5601_ = lean_nat_dec_lt(v___x_5600_, v_size_5594_);
lean_dec(v___x_5600_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5605_; 
lean_dec(v_r_5598_);
v___x_5602_ = lean_nat_add(v___x_5592_, v_size_5594_);
v___x_5603_ = lean_nat_add(v___x_5602_, v_size_5593_);
lean_dec(v___x_5602_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 3, v_impl_5591_);
lean_ctor_set(v___x_5449_, 0, v___x_5603_);
v___x_5605_ = v___x_5449_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5603_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5606_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5606_, 3, v_impl_5591_);
lean_ctor_set(v_reuseFailAlloc_5606_, 4, v_r_5447_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
else
{
lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5672_; 
lean_inc(v_l_5597_);
lean_inc(v_v_5596_);
lean_inc(v_k_5595_);
lean_inc(v_size_5594_);
v_isSharedCheck_5672_ = !lean_is_exclusive(v_impl_5591_);
if (v_isSharedCheck_5672_ == 0)
{
lean_object* v_unused_5673_; lean_object* v_unused_5674_; lean_object* v_unused_5675_; lean_object* v_unused_5676_; lean_object* v_unused_5677_; 
v_unused_5673_ = lean_ctor_get(v_impl_5591_, 4);
lean_dec(v_unused_5673_);
v_unused_5674_ = lean_ctor_get(v_impl_5591_, 3);
lean_dec(v_unused_5674_);
v_unused_5675_ = lean_ctor_get(v_impl_5591_, 2);
lean_dec(v_unused_5675_);
v_unused_5676_ = lean_ctor_get(v_impl_5591_, 1);
lean_dec(v_unused_5676_);
v_unused_5677_ = lean_ctor_get(v_impl_5591_, 0);
lean_dec(v_unused_5677_);
v___x_5608_ = v_impl_5591_;
v_isShared_5609_ = v_isSharedCheck_5672_;
goto v_resetjp_5607_;
}
else
{
lean_dec(v_impl_5591_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5672_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v_size_5610_; lean_object* v_size_5611_; lean_object* v_k_5612_; lean_object* v_v_5613_; lean_object* v_l_5614_; lean_object* v_r_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; uint8_t v___x_5618_; 
v_size_5610_ = lean_ctor_get(v_l_5597_, 0);
v_size_5611_ = lean_ctor_get(v_r_5598_, 0);
v_k_5612_ = lean_ctor_get(v_r_5598_, 1);
v_v_5613_ = lean_ctor_get(v_r_5598_, 2);
v_l_5614_ = lean_ctor_get(v_r_5598_, 3);
v_r_5615_ = lean_ctor_get(v_r_5598_, 4);
v___x_5616_ = lean_unsigned_to_nat(2u);
v___x_5617_ = lean_nat_mul(v___x_5616_, v_size_5610_);
v___x_5618_ = lean_nat_dec_lt(v_size_5611_, v___x_5617_);
lean_dec(v___x_5617_);
if (v___x_5618_ == 0)
{
lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5647_; 
lean_inc(v_r_5615_);
lean_inc(v_l_5614_);
lean_inc(v_v_5613_);
lean_inc(v_k_5612_);
v_isSharedCheck_5647_ = !lean_is_exclusive(v_r_5598_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; lean_object* v_unused_5649_; lean_object* v_unused_5650_; lean_object* v_unused_5651_; lean_object* v_unused_5652_; 
v_unused_5648_ = lean_ctor_get(v_r_5598_, 4);
lean_dec(v_unused_5648_);
v_unused_5649_ = lean_ctor_get(v_r_5598_, 3);
lean_dec(v_unused_5649_);
v_unused_5650_ = lean_ctor_get(v_r_5598_, 2);
lean_dec(v_unused_5650_);
v_unused_5651_ = lean_ctor_get(v_r_5598_, 1);
lean_dec(v_unused_5651_);
v_unused_5652_ = lean_ctor_get(v_r_5598_, 0);
lean_dec(v_unused_5652_);
v___x_5620_ = v_r_5598_;
v_isShared_5621_ = v_isSharedCheck_5647_;
goto v_resetjp_5619_;
}
else
{
lean_dec(v_r_5598_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5647_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___y_5625_; lean_object* v___y_5626_; lean_object* v___y_5627_; lean_object* v___x_5635_; lean_object* v___y_5637_; 
v___x_5622_ = lean_nat_add(v___x_5592_, v_size_5594_);
lean_dec(v_size_5594_);
v___x_5623_ = lean_nat_add(v___x_5622_, v_size_5593_);
lean_dec(v___x_5622_);
v___x_5635_ = lean_nat_add(v___x_5592_, v_size_5610_);
if (lean_obj_tag(v_l_5614_) == 0)
{
lean_object* v_size_5645_; 
v_size_5645_ = lean_ctor_get(v_l_5614_, 0);
lean_inc(v_size_5645_);
v___y_5637_ = v_size_5645_;
goto v___jp_5636_;
}
else
{
lean_object* v___x_5646_; 
v___x_5646_ = lean_unsigned_to_nat(0u);
v___y_5637_ = v___x_5646_;
goto v___jp_5636_;
}
v___jp_5624_:
{
lean_object* v___x_5628_; lean_object* v___x_5630_; 
v___x_5628_ = lean_nat_add(v___y_5626_, v___y_5627_);
lean_dec(v___y_5627_);
lean_dec(v___y_5626_);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_r_5447_);
lean_ctor_set(v___x_5620_, 3, v_r_5615_);
lean_ctor_set(v___x_5620_, 2, v_v_5445_);
lean_ctor_set(v___x_5620_, 1, v_k_5444_);
lean_ctor_set(v___x_5620_, 0, v___x_5628_);
v___x_5630_ = v___x_5620_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5628_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5634_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5634_, 3, v_r_5615_);
lean_ctor_set(v_reuseFailAlloc_5634_, 4, v_r_5447_);
v___x_5630_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5632_; 
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 4, v___x_5630_);
lean_ctor_set(v___x_5608_, 3, v___y_5625_);
lean_ctor_set(v___x_5608_, 2, v_v_5613_);
lean_ctor_set(v___x_5608_, 1, v_k_5612_);
lean_ctor_set(v___x_5608_, 0, v___x_5623_);
v___x_5632_ = v___x_5608_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5623_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_k_5612_);
lean_ctor_set(v_reuseFailAlloc_5633_, 2, v_v_5613_);
lean_ctor_set(v_reuseFailAlloc_5633_, 3, v___y_5625_);
lean_ctor_set(v_reuseFailAlloc_5633_, 4, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
v___jp_5636_:
{
lean_object* v___x_5638_; lean_object* v___x_5640_; 
v___x_5638_ = lean_nat_add(v___x_5635_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec(v___x_5635_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_l_5614_);
lean_ctor_set(v___x_5449_, 3, v_l_5597_);
lean_ctor_set(v___x_5449_, 2, v_v_5596_);
lean_ctor_set(v___x_5449_, 1, v_k_5595_);
lean_ctor_set(v___x_5449_, 0, v___x_5638_);
v___x_5640_ = v___x_5449_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5638_);
lean_ctor_set(v_reuseFailAlloc_5644_, 1, v_k_5595_);
lean_ctor_set(v_reuseFailAlloc_5644_, 2, v_v_5596_);
lean_ctor_set(v_reuseFailAlloc_5644_, 3, v_l_5597_);
lean_ctor_set(v_reuseFailAlloc_5644_, 4, v_l_5614_);
v___x_5640_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5641_; 
v___x_5641_ = lean_nat_add(v___x_5592_, v_size_5593_);
if (lean_obj_tag(v_r_5615_) == 0)
{
lean_object* v_size_5642_; 
v_size_5642_ = lean_ctor_get(v_r_5615_, 0);
lean_inc(v_size_5642_);
v___y_5625_ = v___x_5640_;
v___y_5626_ = v___x_5641_;
v___y_5627_ = v_size_5642_;
goto v___jp_5624_;
}
else
{
lean_object* v___x_5643_; 
v___x_5643_ = lean_unsigned_to_nat(0u);
v___y_5625_ = v___x_5640_;
v___y_5626_ = v___x_5641_;
v___y_5627_ = v___x_5643_;
goto v___jp_5624_;
}
}
}
}
}
else
{
lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5658_; 
lean_del_object(v___x_5449_);
v___x_5653_ = lean_nat_add(v___x_5592_, v_size_5594_);
lean_dec(v_size_5594_);
v___x_5654_ = lean_nat_add(v___x_5653_, v_size_5593_);
lean_dec(v___x_5653_);
v___x_5655_ = lean_nat_add(v___x_5592_, v_size_5593_);
v___x_5656_ = lean_nat_add(v___x_5655_, v_size_5611_);
lean_dec(v___x_5655_);
lean_inc_ref(v_r_5447_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 4, v_r_5447_);
lean_ctor_set(v___x_5608_, 3, v_r_5598_);
lean_ctor_set(v___x_5608_, 2, v_v_5445_);
lean_ctor_set(v___x_5608_, 1, v_k_5444_);
lean_ctor_set(v___x_5608_, 0, v___x_5656_);
v___x_5658_ = v___x_5608_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5656_);
lean_ctor_set(v_reuseFailAlloc_5671_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5671_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5671_, 3, v_r_5598_);
lean_ctor_set(v_reuseFailAlloc_5671_, 4, v_r_5447_);
v___x_5658_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
v_isSharedCheck_5665_ = !lean_is_exclusive(v_r_5447_);
if (v_isSharedCheck_5665_ == 0)
{
lean_object* v_unused_5666_; lean_object* v_unused_5667_; lean_object* v_unused_5668_; lean_object* v_unused_5669_; lean_object* v_unused_5670_; 
v_unused_5666_ = lean_ctor_get(v_r_5447_, 4);
lean_dec(v_unused_5666_);
v_unused_5667_ = lean_ctor_get(v_r_5447_, 3);
lean_dec(v_unused_5667_);
v_unused_5668_ = lean_ctor_get(v_r_5447_, 2);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_r_5447_, 1);
lean_dec(v_unused_5669_);
v_unused_5670_ = lean_ctor_get(v_r_5447_, 0);
lean_dec(v_unused_5670_);
v___x_5660_ = v_r_5447_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_dec(v_r_5447_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
lean_ctor_set(v___x_5660_, 4, v___x_5658_);
lean_ctor_set(v___x_5660_, 3, v_l_5597_);
lean_ctor_set(v___x_5660_, 2, v_v_5596_);
lean_ctor_set(v___x_5660_, 1, v_k_5595_);
lean_ctor_set(v___x_5660_, 0, v___x_5654_);
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v___x_5654_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_k_5595_);
lean_ctor_set(v_reuseFailAlloc_5664_, 2, v_v_5596_);
lean_ctor_set(v_reuseFailAlloc_5664_, 3, v_l_5597_);
lean_ctor_set(v_reuseFailAlloc_5664_, 4, v___x_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5678_; 
v_l_5678_ = lean_ctor_get(v_impl_5591_, 3);
if (lean_obj_tag(v_l_5678_) == 0)
{
lean_object* v_r_5679_; lean_object* v_k_5680_; lean_object* v_v_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5692_; 
lean_inc_ref(v_l_5678_);
v_r_5679_ = lean_ctor_get(v_impl_5591_, 4);
v_k_5680_ = lean_ctor_get(v_impl_5591_, 1);
v_v_5681_ = lean_ctor_get(v_impl_5591_, 2);
v_isSharedCheck_5692_ = !lean_is_exclusive(v_impl_5591_);
if (v_isSharedCheck_5692_ == 0)
{
lean_object* v_unused_5693_; lean_object* v_unused_5694_; 
v_unused_5693_ = lean_ctor_get(v_impl_5591_, 3);
lean_dec(v_unused_5693_);
v_unused_5694_ = lean_ctor_get(v_impl_5591_, 0);
lean_dec(v_unused_5694_);
v___x_5683_ = v_impl_5591_;
v_isShared_5684_ = v_isSharedCheck_5692_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_r_5679_);
lean_inc(v_v_5681_);
lean_inc(v_k_5680_);
lean_dec(v_impl_5591_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5692_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5685_; lean_object* v___x_5687_; 
v___x_5685_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5679_);
if (v_isShared_5684_ == 0)
{
lean_ctor_set(v___x_5683_, 3, v_r_5679_);
lean_ctor_set(v___x_5683_, 2, v_v_5445_);
lean_ctor_set(v___x_5683_, 1, v_k_5444_);
lean_ctor_set(v___x_5683_, 0, v___x_5592_);
v___x_5687_ = v___x_5683_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v___x_5592_);
lean_ctor_set(v_reuseFailAlloc_5691_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5691_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5691_, 3, v_r_5679_);
lean_ctor_set(v_reuseFailAlloc_5691_, 4, v_r_5679_);
v___x_5687_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
lean_object* v___x_5689_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v___x_5687_);
lean_ctor_set(v___x_5449_, 3, v_l_5678_);
lean_ctor_set(v___x_5449_, 2, v_v_5681_);
lean_ctor_set(v___x_5449_, 1, v_k_5680_);
lean_ctor_set(v___x_5449_, 0, v___x_5685_);
v___x_5689_ = v___x_5449_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v___x_5685_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v_k_5680_);
lean_ctor_set(v_reuseFailAlloc_5690_, 2, v_v_5681_);
lean_ctor_set(v_reuseFailAlloc_5690_, 3, v_l_5678_);
lean_ctor_set(v_reuseFailAlloc_5690_, 4, v___x_5687_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
}
}
else
{
lean_object* v_r_5695_; 
v_r_5695_ = lean_ctor_get(v_impl_5591_, 4);
lean_inc(v_r_5695_);
if (lean_obj_tag(v_r_5695_) == 0)
{
lean_object* v_k_5696_; lean_object* v_v_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5720_; 
lean_inc(v_l_5678_);
v_k_5696_ = lean_ctor_get(v_impl_5591_, 1);
v_v_5697_ = lean_ctor_get(v_impl_5591_, 2);
v_isSharedCheck_5720_ = !lean_is_exclusive(v_impl_5591_);
if (v_isSharedCheck_5720_ == 0)
{
lean_object* v_unused_5721_; lean_object* v_unused_5722_; lean_object* v_unused_5723_; 
v_unused_5721_ = lean_ctor_get(v_impl_5591_, 4);
lean_dec(v_unused_5721_);
v_unused_5722_ = lean_ctor_get(v_impl_5591_, 3);
lean_dec(v_unused_5722_);
v_unused_5723_ = lean_ctor_get(v_impl_5591_, 0);
lean_dec(v_unused_5723_);
v___x_5699_ = v_impl_5591_;
v_isShared_5700_ = v_isSharedCheck_5720_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_v_5697_);
lean_inc(v_k_5696_);
lean_dec(v_impl_5591_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5720_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v_k_5701_; lean_object* v_v_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5716_; 
v_k_5701_ = lean_ctor_get(v_r_5695_, 1);
v_v_5702_ = lean_ctor_get(v_r_5695_, 2);
v_isSharedCheck_5716_ = !lean_is_exclusive(v_r_5695_);
if (v_isSharedCheck_5716_ == 0)
{
lean_object* v_unused_5717_; lean_object* v_unused_5718_; lean_object* v_unused_5719_; 
v_unused_5717_ = lean_ctor_get(v_r_5695_, 4);
lean_dec(v_unused_5717_);
v_unused_5718_ = lean_ctor_get(v_r_5695_, 3);
lean_dec(v_unused_5718_);
v_unused_5719_ = lean_ctor_get(v_r_5695_, 0);
lean_dec(v_unused_5719_);
v___x_5704_ = v_r_5695_;
v_isShared_5705_ = v_isSharedCheck_5716_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_v_5702_);
lean_inc(v_k_5701_);
lean_dec(v_r_5695_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5716_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5706_; lean_object* v___x_5708_; 
v___x_5706_ = lean_unsigned_to_nat(3u);
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 4, v_l_5678_);
lean_ctor_set(v___x_5704_, 3, v_l_5678_);
lean_ctor_set(v___x_5704_, 2, v_v_5697_);
lean_ctor_set(v___x_5704_, 1, v_k_5696_);
lean_ctor_set(v___x_5704_, 0, v___x_5592_);
v___x_5708_ = v___x_5704_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5592_);
lean_ctor_set(v_reuseFailAlloc_5715_, 1, v_k_5696_);
lean_ctor_set(v_reuseFailAlloc_5715_, 2, v_v_5697_);
lean_ctor_set(v_reuseFailAlloc_5715_, 3, v_l_5678_);
lean_ctor_set(v_reuseFailAlloc_5715_, 4, v_l_5678_);
v___x_5708_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
lean_object* v___x_5710_; 
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 4, v_l_5678_);
lean_ctor_set(v___x_5699_, 2, v_v_5445_);
lean_ctor_set(v___x_5699_, 1, v_k_5444_);
lean_ctor_set(v___x_5699_, 0, v___x_5592_);
v___x_5710_ = v___x_5699_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v___x_5592_);
lean_ctor_set(v_reuseFailAlloc_5714_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5714_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5714_, 3, v_l_5678_);
lean_ctor_set(v_reuseFailAlloc_5714_, 4, v_l_5678_);
v___x_5710_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
lean_object* v___x_5712_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v___x_5710_);
lean_ctor_set(v___x_5449_, 3, v___x_5708_);
lean_ctor_set(v___x_5449_, 2, v_v_5702_);
lean_ctor_set(v___x_5449_, 1, v_k_5701_);
lean_ctor_set(v___x_5449_, 0, v___x_5706_);
v___x_5712_ = v___x_5449_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5706_);
lean_ctor_set(v_reuseFailAlloc_5713_, 1, v_k_5701_);
lean_ctor_set(v_reuseFailAlloc_5713_, 2, v_v_5702_);
lean_ctor_set(v_reuseFailAlloc_5713_, 3, v___x_5708_);
lean_ctor_set(v_reuseFailAlloc_5713_, 4, v___x_5710_);
v___x_5712_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
return v___x_5712_;
}
}
}
}
}
}
else
{
lean_object* v___x_5724_; lean_object* v___x_5726_; 
v___x_5724_ = lean_unsigned_to_nat(2u);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_r_5695_);
lean_ctor_set(v___x_5449_, 3, v_impl_5591_);
lean_ctor_set(v___x_5449_, 0, v___x_5724_);
v___x_5726_ = v___x_5449_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5724_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5727_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5727_, 3, v_impl_5591_);
lean_ctor_set(v_reuseFailAlloc_5727_, 4, v_r_5695_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5729_; lean_object* v___x_5730_; 
v___x_5729_ = lean_unsigned_to_nat(1u);
v___x_5730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5729_);
lean_ctor_set(v___x_5730_, 1, v_k_5440_);
lean_ctor_set(v___x_5730_, 2, v_v_5441_);
lean_ctor_set(v___x_5730_, 3, v_t_5442_);
lean_ctor_set(v___x_5730_, 4, v_t_5442_);
return v___x_5730_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5731_, lean_object* v_t_5732_){
_start:
{
if (lean_obj_tag(v_t_5732_) == 0)
{
lean_object* v_k_5733_; lean_object* v_l_5734_; lean_object* v_r_5735_; uint8_t v___x_5736_; 
v_k_5733_ = lean_ctor_get(v_t_5732_, 1);
v_l_5734_ = lean_ctor_get(v_t_5732_, 3);
v_r_5735_ = lean_ctor_get(v_t_5732_, 4);
v___x_5736_ = lean_nat_dec_lt(v_k_5733_, v_k_5731_);
if (v___x_5736_ == 0)
{
uint8_t v___x_5737_; 
v___x_5737_ = lean_nat_dec_eq(v_k_5733_, v_k_5731_);
if (v___x_5737_ == 0)
{
v_t_5732_ = v_r_5735_;
goto _start;
}
else
{
return v___x_5737_;
}
}
else
{
v_t_5732_ = v_l_5734_;
goto _start;
}
}
else
{
uint8_t v___x_5740_; 
v___x_5740_ = 0;
return v___x_5740_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5741_, lean_object* v_t_5742_){
_start:
{
uint8_t v_res_5743_; lean_object* v_r_5744_; 
v_res_5743_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5741_, v_t_5742_);
lean_dec(v_t_5742_);
lean_dec(v_k_5741_);
v_r_5744_ = lean_box(v_res_5743_);
return v_r_5744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5745_, lean_object* v_e_5746_){
_start:
{
lean_object* v_defaultInstances_5747_; lean_object* v_priorities_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5775_; 
v_defaultInstances_5747_ = lean_ctor_get(v_d_5745_, 0);
v_priorities_5748_ = lean_ctor_get(v_d_5745_, 1);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_d_5745_);
if (v_isSharedCheck_5775_ == 0)
{
v___x_5750_ = v_d_5745_;
v_isShared_5751_ = v_isSharedCheck_5775_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_priorities_5748_);
lean_inc(v_defaultInstances_5747_);
lean_dec(v_d_5745_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5775_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v_className_5752_; lean_object* v_instanceName_5753_; lean_object* v_priority_5754_; lean_object* v___y_5756_; uint8_t v___x_5772_; 
v_className_5752_ = lean_ctor_get(v_e_5746_, 0);
lean_inc(v_className_5752_);
v_instanceName_5753_ = lean_ctor_get(v_e_5746_, 1);
lean_inc(v_instanceName_5753_);
v_priority_5754_ = lean_ctor_get(v_e_5746_, 2);
lean_inc(v_priority_5754_);
lean_dec_ref(v_e_5746_);
v___x_5772_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5754_, v_priorities_5748_);
if (v___x_5772_ == 0)
{
lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5773_ = lean_box(0);
lean_inc(v_priority_5754_);
v___x_5774_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5754_, v___x_5773_, v_priorities_5748_);
v___y_5756_ = v___x_5774_;
goto v___jp_5755_;
}
else
{
v___y_5756_ = v_priorities_5748_;
goto v___jp_5755_;
}
v___jp_5755_:
{
lean_object* v___x_5757_; 
v___x_5757_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5747_, v_className_5752_);
if (lean_obj_tag(v___x_5757_) == 0)
{
lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5763_; 
v___x_5758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5758_, 0, v_instanceName_5753_);
lean_ctor_set(v___x_5758_, 1, v_priority_5754_);
v___x_5759_ = lean_box(0);
v___x_5760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5758_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5752_, v___x_5760_, v_defaultInstances_5747_);
if (v_isShared_5751_ == 0)
{
lean_ctor_set(v___x_5750_, 1, v___y_5756_);
lean_ctor_set(v___x_5750_, 0, v___x_5761_);
v___x_5763_ = v___x_5750_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5764_, 1, v___y_5756_);
v___x_5763_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
return v___x_5763_;
}
}
else
{
lean_object* v_val_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5770_; 
v_val_5765_ = lean_ctor_get(v___x_5757_, 0);
lean_inc(v_val_5765_);
lean_dec_ref_known(v___x_5757_, 1);
v___x_5766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5766_, 0, v_instanceName_5753_);
lean_ctor_set(v___x_5766_, 1, v_priority_5754_);
v___x_5767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
lean_ctor_set(v___x_5767_, 1, v_val_5765_);
v___x_5768_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5752_, v___x_5767_, v_defaultInstances_5747_);
if (v_isShared_5751_ == 0)
{
lean_ctor_set(v___x_5750_, 1, v___y_5756_);
lean_ctor_set(v___x_5750_, 0, v___x_5768_);
v___x_5770_ = v___x_5750_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5768_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v___y_5756_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5776_, lean_object* v_k_5777_, lean_object* v_t_5778_){
_start:
{
uint8_t v___x_5779_; 
v___x_5779_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5777_, v_t_5778_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5780_, lean_object* v_k_5781_, lean_object* v_t_5782_){
_start:
{
uint8_t v_res_5783_; lean_object* v_r_5784_; 
v_res_5783_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5780_, v_k_5781_, v_t_5782_);
lean_dec(v_t_5782_);
lean_dec(v_k_5781_);
v_r_5784_ = lean_box(v_res_5783_);
return v_r_5784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5785_, lean_object* v_k_5786_, lean_object* v_v_5787_, lean_object* v_t_5788_, lean_object* v_hl_5789_){
_start:
{
lean_object* v___x_5790_; 
v___x_5790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5786_, v_v_5787_, v_t_5788_);
return v___x_5790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5791_, lean_object* v_as_5792_, size_t v_i_5793_, size_t v_stop_5794_, lean_object* v_b_5795_){
_start:
{
lean_object* v___y_5797_; uint8_t v___x_5801_; 
v___x_5801_ = lean_usize_dec_eq(v_i_5793_, v_stop_5794_);
if (v___x_5801_ == 0)
{
lean_object* v___x_5802_; lean_object* v_instanceName_5803_; uint8_t v___x_5804_; lean_object* v___x_5805_; uint8_t v___x_5806_; 
v___x_5802_ = lean_array_uget_borrowed(v_as_5792_, v_i_5793_);
v_instanceName_5803_ = lean_ctor_get(v___x_5802_, 1);
v___x_5804_ = 1;
lean_inc_ref(v_env_5791_);
v___x_5805_ = l_Lean_Environment_setExporting(v_env_5791_, v___x_5804_);
lean_inc(v_instanceName_5803_);
v___x_5806_ = l_Lean_Environment_contains(v___x_5805_, v_instanceName_5803_, v___x_5801_);
if (v___x_5806_ == 0)
{
v___y_5797_ = v_b_5795_;
goto v___jp_5796_;
}
else
{
lean_object* v___x_5807_; 
lean_inc(v___x_5802_);
v___x_5807_ = lean_array_push(v_b_5795_, v___x_5802_);
v___y_5797_ = v___x_5807_;
goto v___jp_5796_;
}
}
else
{
lean_dec_ref(v_env_5791_);
return v_b_5795_;
}
v___jp_5796_:
{
size_t v___x_5798_; size_t v___x_5799_; 
v___x_5798_ = ((size_t)1ULL);
v___x_5799_ = lean_usize_add(v_i_5793_, v___x_5798_);
v_i_5793_ = v___x_5799_;
v_b_5795_ = v___y_5797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5808_, lean_object* v_as_5809_, lean_object* v_i_5810_, lean_object* v_stop_5811_, lean_object* v_b_5812_){
_start:
{
size_t v_i_boxed_5813_; size_t v_stop_boxed_5814_; lean_object* v_res_5815_; 
v_i_boxed_5813_ = lean_unbox_usize(v_i_5810_);
lean_dec(v_i_5810_);
v_stop_boxed_5814_ = lean_unbox_usize(v_stop_5811_);
lean_dec(v_stop_5811_);
v_res_5815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5808_, v_as_5809_, v_i_boxed_5813_, v_stop_boxed_5814_, v_b_5812_);
lean_dec_ref(v_as_5809_);
return v_res_5815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5818_, lean_object* v_x_5819_, lean_object* v_entries_5820_){
_start:
{
lean_object* v_all_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; uint8_t v___x_5825_; 
v_all_5821_ = lean_array_mk(v_entries_5820_);
v___x_5822_ = lean_unsigned_to_nat(0u);
v___x_5823_ = lean_array_get_size(v_all_5821_);
v___x_5824_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5825_ = lean_nat_dec_lt(v___x_5822_, v___x_5823_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; 
lean_dec_ref(v_env_5818_);
v___x_5826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5824_);
lean_ctor_set(v___x_5826_, 1, v___x_5824_);
lean_ctor_set(v___x_5826_, 2, v_all_5821_);
return v___x_5826_;
}
else
{
uint8_t v___x_5827_; 
v___x_5827_ = lean_nat_dec_le(v___x_5823_, v___x_5823_);
if (v___x_5827_ == 0)
{
if (v___x_5825_ == 0)
{
lean_object* v___x_5828_; 
lean_dec_ref(v_env_5818_);
v___x_5828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5828_, 0, v___x_5824_);
lean_ctor_set(v___x_5828_, 1, v___x_5824_);
lean_ctor_set(v___x_5828_, 2, v_all_5821_);
return v___x_5828_;
}
else
{
size_t v___x_5829_; size_t v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5829_ = ((size_t)0ULL);
v___x_5830_ = lean_usize_of_nat(v___x_5823_);
v___x_5831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5818_, v_all_5821_, v___x_5829_, v___x_5830_, v___x_5824_);
lean_inc_ref(v___x_5831_);
v___x_5832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5831_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
lean_ctor_set(v___x_5832_, 2, v_all_5821_);
return v___x_5832_;
}
}
else
{
size_t v___x_5833_; size_t v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5833_ = ((size_t)0ULL);
v___x_5834_ = lean_usize_of_nat(v___x_5823_);
v___x_5835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5818_, v_all_5821_, v___x_5833_, v___x_5834_, v___x_5824_);
lean_inc_ref(v___x_5835_);
v___x_5836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5835_);
lean_ctor_set(v___x_5836_, 1, v___x_5835_);
lean_ctor_set(v___x_5836_, 2, v_all_5821_);
return v___x_5836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5837_, lean_object* v_x_5838_, lean_object* v_entries_5839_){
_start:
{
lean_object* v_res_5840_; 
v_res_5840_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5837_, v_x_5838_, v_entries_5839_);
lean_dec_ref(v_x_5838_);
return v_res_5840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5841_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = lean_array_mk(v_es_5841_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5843_, size_t v_i_5844_, size_t v_stop_5845_, lean_object* v_b_5846_){
_start:
{
uint8_t v___x_5847_; 
v___x_5847_ = lean_usize_dec_eq(v_i_5844_, v_stop_5845_);
if (v___x_5847_ == 0)
{
lean_object* v___x_5848_; lean_object* v___x_5849_; size_t v___x_5850_; size_t v___x_5851_; 
v___x_5848_ = lean_array_uget_borrowed(v_as_5843_, v_i_5844_);
lean_inc(v___x_5848_);
v___x_5849_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5846_, v___x_5848_);
v___x_5850_ = ((size_t)1ULL);
v___x_5851_ = lean_usize_add(v_i_5844_, v___x_5850_);
v_i_5844_ = v___x_5851_;
v_b_5846_ = v___x_5849_;
goto _start;
}
else
{
return v_b_5846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5853_, lean_object* v_i_5854_, lean_object* v_stop_5855_, lean_object* v_b_5856_){
_start:
{
size_t v_i_boxed_5857_; size_t v_stop_boxed_5858_; lean_object* v_res_5859_; 
v_i_boxed_5857_ = lean_unbox_usize(v_i_5854_);
lean_dec(v_i_5854_);
v_stop_boxed_5858_ = lean_unbox_usize(v_stop_5855_);
lean_dec(v_stop_5855_);
v_res_5859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5853_, v_i_boxed_5857_, v_stop_boxed_5858_, v_b_5856_);
lean_dec_ref(v_as_5853_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5860_, size_t v_i_5861_, size_t v_stop_5862_, lean_object* v_b_5863_){
_start:
{
lean_object* v___y_5865_; uint8_t v___x_5869_; 
v___x_5869_ = lean_usize_dec_eq(v_i_5861_, v_stop_5862_);
if (v___x_5869_ == 0)
{
lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; uint8_t v___x_5873_; 
v___x_5870_ = lean_array_uget_borrowed(v_as_5860_, v_i_5861_);
v___x_5871_ = lean_unsigned_to_nat(0u);
v___x_5872_ = lean_array_get_size(v___x_5870_);
v___x_5873_ = lean_nat_dec_lt(v___x_5871_, v___x_5872_);
if (v___x_5873_ == 0)
{
v___y_5865_ = v_b_5863_;
goto v___jp_5864_;
}
else
{
size_t v___x_5874_; size_t v___x_5875_; lean_object* v___x_5876_; 
v___x_5874_ = ((size_t)0ULL);
v___x_5875_ = lean_usize_of_nat(v___x_5872_);
v___x_5876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5870_, v___x_5874_, v___x_5875_, v_b_5863_);
v___y_5865_ = v___x_5876_;
goto v___jp_5864_;
}
}
else
{
return v_b_5863_;
}
v___jp_5864_:
{
size_t v___x_5866_; size_t v___x_5867_; 
v___x_5866_ = ((size_t)1ULL);
v___x_5867_ = lean_usize_add(v_i_5861_, v___x_5866_);
v_i_5861_ = v___x_5867_;
v_b_5863_ = v___y_5865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5877_, lean_object* v_i_5878_, lean_object* v_stop_5879_, lean_object* v_b_5880_){
_start:
{
size_t v_i_boxed_5881_; size_t v_stop_boxed_5882_; lean_object* v_res_5883_; 
v_i_boxed_5881_ = lean_unbox_usize(v_i_5878_);
lean_dec(v_i_5878_);
v_stop_boxed_5882_ = lean_unbox_usize(v_stop_5879_);
lean_dec(v_stop_5879_);
v_res_5883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5877_, v_i_boxed_5881_, v_stop_boxed_5882_, v_b_5880_);
lean_dec_ref(v_as_5877_);
return v_res_5883_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5884_, lean_object* v_as_5885_){
_start:
{
lean_object* v___x_5886_; lean_object* v___x_5887_; uint8_t v___x_5888_; 
v___x_5886_ = lean_unsigned_to_nat(0u);
v___x_5887_ = lean_array_get_size(v_as_5885_);
v___x_5888_ = lean_nat_dec_lt(v___x_5886_, v___x_5887_);
if (v___x_5888_ == 0)
{
return v_initState_5884_;
}
else
{
size_t v___x_5889_; size_t v___x_5890_; lean_object* v___x_5891_; 
v___x_5889_ = ((size_t)0ULL);
v___x_5890_ = lean_usize_of_nat(v___x_5887_);
v___x_5891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5885_, v___x_5889_, v___x_5890_, v_initState_5884_);
return v___x_5891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5892_, lean_object* v_as_5893_){
_start:
{
lean_object* v_res_5894_; 
v_res_5894_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5892_, v_as_5893_);
lean_dec_ref(v_as_5893_);
return v_res_5894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5895_){
_start:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5896_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5897_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5896_, v_es_5895_);
return v___x_5897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5898_){
_start:
{
lean_object* v_res_5899_; 
v_res_5899_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5898_);
lean_dec_ref(v_es_5898_);
return v_res_5899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5921_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5922_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5921_);
return v___x_5922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5923_){
_start:
{
lean_object* v_res_5924_; 
v_res_5924_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5924_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_){
_start:
{
lean_object* v___x_5929_; lean_object* v_nextMacroScope_5930_; lean_object* v_ngen_5931_; lean_object* v_auxDeclNGen_5932_; lean_object* v_traceState_5933_; lean_object* v_recordedDeps_5934_; lean_object* v_messages_5935_; lean_object* v_infoState_5936_; lean_object* v_snapshotTasks_5937_; lean_object* v___x_5939_; uint8_t v_isShared_5940_; uint8_t v_isSharedCheck_5963_; 
v___x_5929_ = lean_st_ref_take(v___y_5927_);
v_nextMacroScope_5930_ = lean_ctor_get(v___x_5929_, 1);
v_ngen_5931_ = lean_ctor_get(v___x_5929_, 2);
v_auxDeclNGen_5932_ = lean_ctor_get(v___x_5929_, 3);
v_traceState_5933_ = lean_ctor_get(v___x_5929_, 4);
v_recordedDeps_5934_ = lean_ctor_get(v___x_5929_, 6);
v_messages_5935_ = lean_ctor_get(v___x_5929_, 7);
v_infoState_5936_ = lean_ctor_get(v___x_5929_, 8);
v_snapshotTasks_5937_ = lean_ctor_get(v___x_5929_, 9);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5963_ == 0)
{
lean_object* v_unused_5964_; lean_object* v_unused_5965_; 
v_unused_5964_ = lean_ctor_get(v___x_5929_, 5);
lean_dec(v_unused_5964_);
v_unused_5965_ = lean_ctor_get(v___x_5929_, 0);
lean_dec(v_unused_5965_);
v___x_5939_ = v___x_5929_;
v_isShared_5940_ = v_isSharedCheck_5963_;
goto v_resetjp_5938_;
}
else
{
lean_inc(v_snapshotTasks_5937_);
lean_inc(v_infoState_5936_);
lean_inc(v_messages_5935_);
lean_inc(v_recordedDeps_5934_);
lean_inc(v_traceState_5933_);
lean_inc(v_auxDeclNGen_5932_);
lean_inc(v_ngen_5931_);
lean_inc(v_nextMacroScope_5930_);
lean_dec(v___x_5929_);
v___x_5939_ = lean_box(0);
v_isShared_5940_ = v_isSharedCheck_5963_;
goto v_resetjp_5938_;
}
v_resetjp_5938_:
{
lean_object* v___x_5941_; lean_object* v___x_5943_; 
v___x_5941_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_5940_ == 0)
{
lean_ctor_set(v___x_5939_, 5, v___x_5941_);
lean_ctor_set(v___x_5939_, 0, v_env_5925_);
v___x_5943_ = v___x_5939_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_env_5925_);
lean_ctor_set(v_reuseFailAlloc_5962_, 1, v_nextMacroScope_5930_);
lean_ctor_set(v_reuseFailAlloc_5962_, 2, v_ngen_5931_);
lean_ctor_set(v_reuseFailAlloc_5962_, 3, v_auxDeclNGen_5932_);
lean_ctor_set(v_reuseFailAlloc_5962_, 4, v_traceState_5933_);
lean_ctor_set(v_reuseFailAlloc_5962_, 5, v___x_5941_);
lean_ctor_set(v_reuseFailAlloc_5962_, 6, v_recordedDeps_5934_);
lean_ctor_set(v_reuseFailAlloc_5962_, 7, v_messages_5935_);
lean_ctor_set(v_reuseFailAlloc_5962_, 8, v_infoState_5936_);
lean_ctor_set(v_reuseFailAlloc_5962_, 9, v_snapshotTasks_5937_);
v___x_5943_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v_mctx_5946_; lean_object* v_zetaDeltaFVarIds_5947_; lean_object* v_postponed_5948_; lean_object* v_diag_5949_; lean_object* v___x_5951_; uint8_t v_isShared_5952_; uint8_t v_isSharedCheck_5960_; 
v___x_5944_ = lean_st_ref_put(v___y_5927_, v___x_5943_);
v___x_5945_ = lean_st_ref_take(v___y_5926_);
v_mctx_5946_ = lean_ctor_get(v___x_5945_, 0);
v_zetaDeltaFVarIds_5947_ = lean_ctor_get(v___x_5945_, 2);
v_postponed_5948_ = lean_ctor_get(v___x_5945_, 3);
v_diag_5949_ = lean_ctor_get(v___x_5945_, 4);
v_isSharedCheck_5960_ = !lean_is_exclusive(v___x_5945_);
if (v_isSharedCheck_5960_ == 0)
{
lean_object* v_unused_5961_; 
v_unused_5961_ = lean_ctor_get(v___x_5945_, 1);
lean_dec(v_unused_5961_);
v___x_5951_ = v___x_5945_;
v_isShared_5952_ = v_isSharedCheck_5960_;
goto v_resetjp_5950_;
}
else
{
lean_inc(v_diag_5949_);
lean_inc(v_postponed_5948_);
lean_inc(v_zetaDeltaFVarIds_5947_);
lean_inc(v_mctx_5946_);
lean_dec(v___x_5945_);
v___x_5951_ = lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5960_;
goto v_resetjp_5950_;
}
v_resetjp_5950_:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5956_; 
v___x_5953_ = lean_box(0);
v___x_5954_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5952_ == 0)
{
lean_ctor_set(v___x_5951_, 1, v___x_5954_);
v___x_5956_ = v___x_5951_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5959_; 
v_reuseFailAlloc_5959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_mctx_5946_);
lean_ctor_set(v_reuseFailAlloc_5959_, 1, v___x_5954_);
lean_ctor_set(v_reuseFailAlloc_5959_, 2, v_zetaDeltaFVarIds_5947_);
lean_ctor_set(v_reuseFailAlloc_5959_, 3, v_postponed_5948_);
lean_ctor_set(v_reuseFailAlloc_5959_, 4, v_diag_5949_);
v___x_5956_ = v_reuseFailAlloc_5959_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5957_ = lean_st_ref_put(v___y_5926_, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5953_);
return v___x_5958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_){
_start:
{
lean_object* v_res_5970_; 
v_res_5970_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5966_, v___y_5967_, v___y_5968_);
lean_dec(v___y_5968_);
lean_dec(v___y_5967_);
return v_res_5970_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5971_, v___y_5973_, v___y_5975_);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_){
_start:
{
lean_object* v_res_5984_; 
v_res_5984_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_);
lean_dec(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
return v_res_5984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v___x_5985_, lean_object* v___x_5986_, lean_object* v_s_5987_){
_start:
{
lean_object* v_addEntryFn_5988_; lean_object* v_importedEntries_5989_; lean_object* v_state_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_5998_; 
v_addEntryFn_5988_ = lean_ctor_get(v___x_5985_, 3);
lean_inc(v_addEntryFn_5988_);
lean_dec_ref(v___x_5985_);
v_importedEntries_5989_ = lean_ctor_get(v_s_5987_, 0);
v_state_5990_ = lean_ctor_get(v_s_5987_, 1);
v_isSharedCheck_5998_ = !lean_is_exclusive(v_s_5987_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5992_ = v_s_5987_;
v_isShared_5993_ = v_isSharedCheck_5998_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_state_5990_);
lean_inc(v_importedEntries_5989_);
lean_dec(v_s_5987_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_5998_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v_state_5994_; lean_object* v___x_5996_; 
v_state_5994_ = lean_apply_2(v_addEntryFn_5988_, v_state_5990_, v___x_5986_);
if (v_isShared_5993_ == 0)
{
lean_ctor_set(v___x_5992_, 1, v_state_5994_);
v___x_5996_ = v___x_5992_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_importedEntries_5989_);
lean_ctor_set(v_reuseFailAlloc_5997_, 1, v_state_5994_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
return v___x_5996_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_6000_; lean_object* v___x_6001_; 
v___x_6000_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__0));
v___x_6001_ = l_Lean_stringToMessageData(v___x_6000_);
return v___x_6001_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3(void){
_start:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; 
v___x_6003_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__2));
v___x_6004_ = l_Lean_stringToMessageData(v___x_6003_);
return v___x_6004_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5(void){
_start:
{
lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6006_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__4));
v___x_6007_ = l_Lean_stringToMessageData(v___x_6006_);
return v___x_6007_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7(void){
_start:
{
lean_object* v___x_6009_; lean_object* v___x_6010_; 
v___x_6009_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__6));
v___x_6010_ = l_Lean_stringToMessageData(v___x_6009_);
return v___x_6010_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9(void){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6012_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__8));
v___x_6013_ = l_Lean_stringToMessageData(v___x_6012_);
return v___x_6013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1(lean_object* v_declName_6014_, lean_object* v_prio_6015_, lean_object* v_x_6016_, lean_object* v_type_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v___x_6023_; 
v___x_6023_ = l_Lean_Expr_getAppFn(v_type_6017_);
if (lean_obj_tag(v___x_6023_) == 4)
{
lean_object* v_declName_6024_; lean_object* v___y_6026_; lean_object* v___y_6027_; lean_object* v___y_6028_; lean_object* v___y_6029_; lean_object* v___x_6045_; lean_object* v_env_6046_; uint8_t v___x_6047_; 
v_declName_6024_ = lean_ctor_get(v___x_6023_, 0);
lean_inc(v_declName_6024_);
lean_dec_ref_known(v___x_6023_, 2);
v___x_6045_ = lean_st_ref_get(v___y_6021_);
v_env_6046_ = lean_ctor_get(v___x_6045_, 0);
lean_inc_ref(v_env_6046_);
lean_dec(v___x_6045_);
v___x_6047_ = l_Lean_isClass(v_env_6046_, v_declName_6024_);
if (v___x_6047_ == 0)
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; 
lean_dec(v_prio_6015_);
v___x_6048_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6049_ = l_Lean_MessageData_ofConstName(v_declName_6014_, v___x_6047_);
v___x_6050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6048_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__3, &l_Lean_Meta_addDefaultInstance___lam__1___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3);
v___x_6052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6050_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
lean_inc(v_declName_6024_);
v___x_6053_ = l_Lean_MessageData_ofName(v_declName_6024_);
v___x_6054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6052_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__5, &l_Lean_Meta_addDefaultInstance___lam__1___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5);
v___x_6056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6054_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = l_Lean_MessageData_ofConstName(v_declName_6024_, v___x_6047_);
v___x_6058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6056_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__7, &l_Lean_Meta_addDefaultInstance___lam__1___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7);
v___x_6060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6058_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6060_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_);
return v___x_6061_;
}
else
{
v___y_6026_ = v___y_6018_;
v___y_6027_ = v___y_6019_;
v___y_6028_ = v___y_6020_;
v___y_6029_ = v___y_6021_;
goto v___jp_6025_;
}
v___jp_6025_:
{
lean_object* v___x_6030_; lean_object* v_env_6031_; lean_object* v___x_6032_; lean_object* v_toEnvExtension_6033_; lean_object* v_asyncMode_6034_; uint8_t v_logWrites_6035_; lean_object* v___x_6036_; lean_object* v___f_6037_; lean_object* v___x_6038_; uint8_t v___x_6039_; 
v___x_6030_ = lean_st_ref_get(v___y_6029_);
v_env_6031_ = lean_ctor_get(v___x_6030_, 0);
lean_inc_ref(v_env_6031_);
lean_dec(v___x_6030_);
v___x_6032_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6033_ = lean_ctor_get(v___x_6032_, 0);
v_asyncMode_6034_ = lean_ctor_get(v_toEnvExtension_6033_, 2);
v_logWrites_6035_ = lean_ctor_get_uint8(v_toEnvExtension_6033_, sizeof(void*)*6);
v___x_6036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6036_, 0, v_declName_6024_);
lean_ctor_set(v___x_6036_, 1, v_declName_6014_);
lean_ctor_set(v___x_6036_, 2, v_prio_6015_);
v___f_6037_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0), 3, 2);
lean_closure_set(v___f_6037_, 0, v___x_6032_);
lean_closure_set(v___f_6037_, 1, v___x_6036_);
v___x_6038_ = lean_box(0);
v___x_6039_ = 1;
if (v_logWrites_6035_ == 0)
{
lean_object* v___x_6040_; lean_object* v___x_6041_; 
lean_inc_ref(v_toEnvExtension_6033_);
v___x_6040_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6033_, v_env_6031_, v___f_6037_, v_asyncMode_6034_, v___x_6038_, v___x_6039_);
v___x_6041_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6040_, v___y_6027_, v___y_6029_);
return v___x_6041_;
}
else
{
lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; 
lean_inc_ref_n(v_toEnvExtension_6033_, 2);
v___x_6042_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_6033_, v_env_6031_);
lean_dec_ref(v_env_6031_);
v___x_6043_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6033_, v___x_6042_, v___f_6037_, v_asyncMode_6034_, v___x_6038_, v___x_6039_);
v___x_6044_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6043_, v___y_6027_, v___y_6029_);
return v___x_6044_;
}
}
}
else
{
lean_object* v___x_6062_; uint8_t v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
lean_dec_ref(v___x_6023_);
lean_dec(v_prio_6015_);
v___x_6062_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6063_ = 0;
v___x_6064_ = l_Lean_MessageData_ofConstName(v_declName_6014_, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6062_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__9, &l_Lean_Meta_addDefaultInstance___lam__1___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9);
v___x_6067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6065_);
lean_ctor_set(v___x_6067_, 1, v___x_6066_);
v___x_6068_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6067_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_);
return v___x_6068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1___boxed(lean_object* v_declName_6069_, lean_object* v_prio_6070_, lean_object* v_x_6071_, lean_object* v_type_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_){
_start:
{
lean_object* v_res_6078_; 
v_res_6078_ = l_Lean_Meta_addDefaultInstance___lam__1(v_declName_6069_, v_prio_6070_, v_x_6071_, v_type_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_);
lean_dec(v___y_6076_);
lean_dec_ref(v___y_6075_);
lean_dec(v___y_6074_);
lean_dec_ref(v___y_6073_);
lean_dec_ref(v_type_6072_);
lean_dec_ref(v_x_6071_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_6079_, lean_object* v_prio_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_){
_start:
{
lean_object* v___f_6086_; lean_object* v___x_6087_; lean_object* v_env_6088_; uint8_t v___x_6089_; lean_object* v___x_6090_; 
lean_inc_n(v_declName_6079_, 2);
v___f_6086_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__1___boxed), 9, 2);
lean_closure_set(v___f_6086_, 0, v_declName_6079_);
lean_closure_set(v___f_6086_, 1, v_prio_6080_);
v___x_6087_ = lean_st_ref_get(v_a_6084_);
v_env_6088_ = lean_ctor_get(v___x_6087_, 0);
lean_inc_ref(v_env_6088_);
lean_dec(v___x_6087_);
v___x_6089_ = 0;
v___x_6090_ = l_Lean_Environment_find_x3f(v_env_6088_, v_declName_6079_, v___x_6089_);
if (lean_obj_tag(v___x_6090_) == 0)
{
lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; 
lean_dec_ref(v___f_6086_);
v___x_6091_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_6092_ = l_Lean_MessageData_ofConstName(v_declName_6079_, v___x_6089_);
v___x_6093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6091_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6093_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6095_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_);
return v___x_6096_;
}
else
{
lean_object* v_val_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; 
lean_dec(v_declName_6079_);
v_val_6097_ = lean_ctor_get(v___x_6090_, 0);
lean_inc(v_val_6097_);
lean_dec_ref_known(v___x_6090_, 1);
v___x_6098_ = l_Lean_ConstantInfo_type(v_val_6097_);
lean_dec(v_val_6097_);
v___x_6099_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_6098_, v___f_6086_, v___x_6089_, v___x_6089_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_);
return v___x_6099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_6100_, lean_object* v_prio_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_){
_start:
{
lean_object* v_res_6107_; 
v_res_6107_ = l_Lean_Meta_addDefaultInstance(v_declName_6100_, v_prio_6101_, v_a_6102_, v_a_6103_, v_a_6104_, v_a_6105_);
lean_dec(v_a_6105_);
lean_dec_ref(v_a_6104_);
lean_dec(v_a_6103_);
lean_dec_ref(v_a_6102_);
return v_res_6107_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6109_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_6110_ = l_Lean_stringToMessageData(v___x_6109_);
return v___x_6110_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6112_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_6113_ = l_Lean_stringToMessageData(v___x_6112_);
return v___x_6113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_6117_, uint8_t v_kind_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_){
_start:
{
lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___y_6128_; 
v___x_6122_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_6123_ = l_Lean_MessageData_ofName(v_name_6117_);
v___x_6124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6122_);
lean_ctor_set(v___x_6124_, 1, v___x_6123_);
v___x_6125_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_6126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6124_);
lean_ctor_set(v___x_6126_, 1, v___x_6125_);
switch(v_kind_6118_)
{
case 0:
{
lean_object* v___x_6135_; 
v___x_6135_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_6128_ = v___x_6135_;
goto v___jp_6127_;
}
case 1:
{
lean_object* v___x_6136_; 
v___x_6136_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_6128_ = v___x_6136_;
goto v___jp_6127_;
}
default: 
{
lean_object* v___x_6137_; 
v___x_6137_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_6128_ = v___x_6137_;
goto v___jp_6127_;
}
}
v___jp_6127_:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; 
lean_inc_ref(v___y_6128_);
v___x_6129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6129_, 0, v___y_6128_);
v___x_6130_ = l_Lean_MessageData_ofFormat(v___x_6129_);
v___x_6131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6126_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6131_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
v___x_6134_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6133_, v___y_6119_, v___y_6120_);
return v___x_6134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6138_, lean_object* v_kind_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
uint8_t v_kind_boxed_6143_; lean_object* v_res_6144_; 
v_kind_boxed_6143_ = lean_unbox(v_kind_6139_);
v_res_6144_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6138_, v_kind_boxed_6143_, v___y_6140_, v___y_6141_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6140_);
return v_res_6144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6145_, lean_object* v___x_6146_, lean_object* v___x_6147_, lean_object* v_declName_6148_, lean_object* v_stx_6149_, uint8_t v_kind_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6154_ = lean_unsigned_to_nat(1u);
v___x_6155_ = l_Lean_Syntax_getArg(v_stx_6149_, v___x_6154_);
v___x_6156_ = l_Lean_getAttrParamOptPrio(v___x_6155_, v___y_6151_, v___y_6152_);
if (lean_obj_tag(v___x_6156_) == 0)
{
lean_object* v_a_6157_; lean_object* v___y_6159_; lean_object* v___y_6160_; uint8_t v___x_6192_; uint8_t v___x_6193_; 
v_a_6157_ = lean_ctor_get(v___x_6156_, 0);
lean_inc(v_a_6157_);
lean_dec_ref_known(v___x_6156_, 1);
v___x_6192_ = 0;
v___x_6193_ = l_Lean_instBEqAttributeKind_beq(v_kind_6150_, v___x_6192_);
if (v___x_6193_ == 0)
{
lean_object* v___x_6194_; 
lean_dec(v_a_6157_);
lean_dec(v_declName_6148_);
lean_dec(v___x_6146_);
lean_dec(v___x_6145_);
v___x_6194_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6147_, v_kind_6150_, v___y_6151_, v___y_6152_);
return v___x_6194_;
}
else
{
lean_dec(v___x_6147_);
v___y_6159_ = v___y_6151_;
v___y_6160_ = v___y_6152_;
goto v___jp_6158_;
}
v___jp_6158_:
{
uint8_t v___x_6161_; uint8_t v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; size_t v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6161_ = 0;
v___x_6162_ = 1;
v___x_6163_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6164_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6165_ = lean_unsigned_to_nat(32u);
v___x_6166_ = lean_mk_empty_array_with_capacity(v___x_6165_);
v___x_6167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_6168_ = ((size_t)5ULL);
lean_inc_n(v___x_6145_, 6);
v___x_6169_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6169_, 0, v___x_6167_);
lean_ctor_set(v___x_6169_, 1, v___x_6166_);
lean_ctor_set(v___x_6169_, 2, v___x_6145_);
lean_ctor_set(v___x_6169_, 3, v___x_6145_);
lean_ctor_set_usize(v___x_6169_, 4, v___x_6168_);
v___x_6170_ = lean_box(1);
lean_inc_ref(v___x_6169_);
v___x_6171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6164_);
lean_ctor_set(v___x_6171_, 1, v___x_6169_);
lean_ctor_set(v___x_6171_, 2, v___x_6170_);
v___x_6172_ = lean_mk_empty_array_with_capacity(v___x_6145_);
v___x_6173_ = lean_box(0);
lean_inc(v___x_6146_);
v___x_6174_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6174_, 0, v___x_6163_);
lean_ctor_set(v___x_6174_, 1, v___x_6146_);
lean_ctor_set(v___x_6174_, 2, v___x_6171_);
lean_ctor_set(v___x_6174_, 3, v___x_6172_);
lean_ctor_set(v___x_6174_, 4, v___x_6173_);
lean_ctor_set(v___x_6174_, 5, v___x_6145_);
lean_ctor_set(v___x_6174_, 6, v___x_6173_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*7, v___x_6161_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*7 + 1, v___x_6161_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*7 + 2, v___x_6161_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*7 + 3, v___x_6162_);
v___x_6175_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_6176_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6145_);
lean_ctor_set(v___x_6176_, 1, v___x_6145_);
lean_ctor_set(v___x_6176_, 2, v___x_6145_);
lean_ctor_set(v___x_6176_, 3, v___x_6145_);
lean_ctor_set(v___x_6176_, 4, v___x_6164_);
lean_ctor_set(v___x_6176_, 5, v___x_6164_);
lean_ctor_set(v___x_6176_, 6, v___x_6164_);
lean_ctor_set(v___x_6176_, 7, v___x_6164_);
lean_ctor_set(v___x_6176_, 8, v___x_6164_);
lean_ctor_set(v___x_6176_, 9, v___x_6164_);
lean_ctor_set(v___x_6176_, 10, v___x_6164_);
lean_ctor_set(v___x_6176_, 11, v___x_6175_);
v___x_6177_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6178_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6176_);
lean_ctor_set(v___x_6179_, 1, v___x_6177_);
lean_ctor_set(v___x_6179_, 2, v___x_6146_);
lean_ctor_set(v___x_6179_, 3, v___x_6169_);
lean_ctor_set(v___x_6179_, 4, v___x_6178_);
v___x_6180_ = lean_box(0);
v___x_6181_ = lean_st_mk_ref(v___x_6179_);
v___x_6182_ = l_Lean_Meta_addDefaultInstance(v_declName_6148_, v_a_6157_, v___x_6174_, v___x_6181_, v___y_6159_, v___y_6160_);
lean_dec_ref_known(v___x_6174_, 7);
if (lean_obj_tag(v___x_6182_) == 0)
{
lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6190_; 
v_isSharedCheck_6190_ = !lean_is_exclusive(v___x_6182_);
if (v_isSharedCheck_6190_ == 0)
{
lean_object* v_unused_6191_; 
v_unused_6191_ = lean_ctor_get(v___x_6182_, 0);
lean_dec(v_unused_6191_);
v___x_6184_ = v___x_6182_;
v_isShared_6185_ = v_isSharedCheck_6190_;
goto v_resetjp_6183_;
}
else
{
lean_dec(v___x_6182_);
v___x_6184_ = lean_box(0);
v_isShared_6185_ = v_isSharedCheck_6190_;
goto v_resetjp_6183_;
}
v_resetjp_6183_:
{
lean_object* v___x_6186_; lean_object* v___x_6188_; 
v___x_6186_ = lean_st_ref_get(v___x_6181_);
lean_dec(v___x_6181_);
lean_dec(v___x_6186_);
if (v_isShared_6185_ == 0)
{
lean_ctor_set(v___x_6184_, 0, v___x_6180_);
v___x_6188_ = v___x_6184_;
goto v_reusejp_6187_;
}
else
{
lean_object* v_reuseFailAlloc_6189_; 
v_reuseFailAlloc_6189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6189_, 0, v___x_6180_);
v___x_6188_ = v_reuseFailAlloc_6189_;
goto v_reusejp_6187_;
}
v_reusejp_6187_:
{
return v___x_6188_;
}
}
}
else
{
lean_dec(v___x_6181_);
return v___x_6182_;
}
}
}
else
{
lean_object* v_a_6195_; lean_object* v___x_6197_; uint8_t v_isShared_6198_; uint8_t v_isSharedCheck_6202_; 
lean_dec(v_declName_6148_);
lean_dec(v___x_6147_);
lean_dec(v___x_6146_);
lean_dec(v___x_6145_);
v_a_6195_ = lean_ctor_get(v___x_6156_, 0);
v_isSharedCheck_6202_ = !lean_is_exclusive(v___x_6156_);
if (v_isSharedCheck_6202_ == 0)
{
v___x_6197_ = v___x_6156_;
v_isShared_6198_ = v_isSharedCheck_6202_;
goto v_resetjp_6196_;
}
else
{
lean_inc(v_a_6195_);
lean_dec(v___x_6156_);
v___x_6197_ = lean_box(0);
v_isShared_6198_ = v_isSharedCheck_6202_;
goto v_resetjp_6196_;
}
v_resetjp_6196_:
{
lean_object* v___x_6200_; 
if (v_isShared_6198_ == 0)
{
v___x_6200_ = v___x_6197_;
goto v_reusejp_6199_;
}
else
{
lean_object* v_reuseFailAlloc_6201_; 
v_reuseFailAlloc_6201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6201_, 0, v_a_6195_);
v___x_6200_ = v_reuseFailAlloc_6201_;
goto v_reusejp_6199_;
}
v_reusejp_6199_:
{
return v___x_6200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6203_, lean_object* v___x_6204_, lean_object* v___x_6205_, lean_object* v_declName_6206_, lean_object* v_stx_6207_, lean_object* v_kind_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
uint8_t v_kind_boxed_6212_; lean_object* v_res_6213_; 
v_kind_boxed_6212_ = lean_unbox(v_kind_6208_);
v_res_6213_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6203_, v___x_6204_, v___x_6205_, v_declName_6206_, v_stx_6207_, v_kind_boxed_6212_, v___y_6209_, v___y_6210_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
lean_dec(v_stx_6207_);
return v_res_6213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6215_; lean_object* v___x_6216_; 
v___x_6215_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6216_ = l_Lean_stringToMessageData(v___x_6215_);
return v___x_6216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6218_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6219_ = l_Lean_stringToMessageData(v___x_6218_);
return v___x_6219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6220_, lean_object* v_decl_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_){
_start:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; 
v___x_6225_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6226_ = l_Lean_MessageData_ofName(v___x_6220_);
v___x_6227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6227_, 0, v___x_6225_);
lean_ctor_set(v___x_6227_, 1, v___x_6226_);
v___x_6228_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6227_);
lean_ctor_set(v___x_6229_, 1, v___x_6228_);
v___x_6230_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6229_, v___y_6222_, v___y_6223_);
return v___x_6230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6231_, lean_object* v_decl_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_){
_start:
{
lean_object* v_res_6236_; 
v_res_6236_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6231_, v_decl_6232_, v___y_6233_, v___y_6234_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v_decl_6232_);
return v_res_6236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; 
v___x_6269_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6270_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6271_ = l_Lean_registerBuiltinAttribute(v___x_6270_);
if (lean_obj_tag(v___x_6271_) == 0)
{
lean_object* v___x_6272_; uint8_t v___x_6273_; lean_object* v___x_6274_; 
lean_dec_ref_known(v___x_6271_, 1);
v___x_6272_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6273_ = 0;
v___x_6274_ = l_Lean_registerTraceClass(v___x_6272_, v___x_6273_, v___x_6269_);
return v___x_6274_;
}
else
{
return v___x_6271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6275_){
_start:
{
lean_object* v_res_6276_; 
v_res_6276_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6277_, lean_object* v_name_6278_, uint8_t v_kind_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_){
_start:
{
lean_object* v___x_6283_; 
v___x_6283_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6278_, v_kind_6279_, v___y_6280_, v___y_6281_);
return v___x_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6284_, lean_object* v_name_6285_, lean_object* v_kind_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_){
_start:
{
uint8_t v_kind_boxed_6290_; lean_object* v_res_6291_; 
v_kind_boxed_6290_ = lean_unbox(v_kind_6286_);
v_res_6291_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6284_, v_name_6285_, v_kind_boxed_6290_, v___y_6287_, v___y_6288_);
lean_dec(v___y_6288_);
lean_dec_ref(v___y_6287_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6292_, lean_object* v_toPure_6293_, lean_object* v_____do__lift_6294_){
_start:
{
lean_object* v___x_6295_; lean_object* v_toEnvExtension_6296_; lean_object* v_asyncMode_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v_priorities_6300_; lean_object* v___x_6301_; 
v___x_6295_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6296_ = lean_ctor_get(v___x_6295_, 0);
v_asyncMode_6297_ = lean_ctor_get(v_toEnvExtension_6296_, 2);
v___x_6298_ = lean_box(0);
v___x_6299_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6292_, v___x_6295_, v_____do__lift_6294_, v_asyncMode_6297_, v___x_6298_);
v_priorities_6300_ = lean_ctor_get(v___x_6299_, 1);
lean_inc(v_priorities_6300_);
lean_dec(v___x_6299_);
v___x_6301_ = lean_apply_2(v_toPure_6293_, lean_box(0), v_priorities_6300_);
return v___x_6301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6302_, lean_object* v_inst_6303_){
_start:
{
lean_object* v_toApplicative_6304_; lean_object* v_toBind_6305_; lean_object* v_getEnv_6306_; lean_object* v_toPure_6307_; lean_object* v___x_6308_; lean_object* v___f_6309_; lean_object* v___x_6310_; 
v_toApplicative_6304_ = lean_ctor_get(v_inst_6302_, 0);
lean_inc_ref(v_toApplicative_6304_);
v_toBind_6305_ = lean_ctor_get(v_inst_6302_, 1);
lean_inc(v_toBind_6305_);
lean_dec_ref(v_inst_6302_);
v_getEnv_6306_ = lean_ctor_get(v_inst_6303_, 0);
lean_inc(v_getEnv_6306_);
lean_dec_ref(v_inst_6303_);
v_toPure_6307_ = lean_ctor_get(v_toApplicative_6304_, 1);
lean_inc(v_toPure_6307_);
lean_dec_ref(v_toApplicative_6304_);
v___x_6308_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6309_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6309_, 0, v___x_6308_);
lean_closure_set(v___f_6309_, 1, v_toPure_6307_);
v___x_6310_ = lean_apply_4(v_toBind_6305_, lean_box(0), lean_box(0), v_getEnv_6306_, v___f_6309_);
return v___x_6310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6311_, lean_object* v_inst_6312_, lean_object* v_inst_6313_){
_start:
{
lean_object* v___x_6314_; 
v___x_6314_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6312_, v_inst_6313_);
return v___x_6314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6315_, uint8_t v_isExporting_6316_, lean_object* v_x_6317_){
_start:
{
lean_object* v_fst_6318_; uint8_t v___x_6319_; 
v_fst_6318_ = lean_ctor_get(v_x_6317_, 0);
lean_inc(v_fst_6318_);
lean_dec_ref(v_x_6317_);
v___x_6319_ = l_Lean_Environment_contains(v_env_6315_, v_fst_6318_, v_isExporting_6316_);
return v___x_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6320_, lean_object* v_isExporting_6321_, lean_object* v_x_6322_){
_start:
{
uint8_t v_isExporting_boxed_6323_; uint8_t v_res_6324_; lean_object* v_r_6325_; 
v_isExporting_boxed_6323_ = lean_unbox(v_isExporting_6321_);
v_res_6324_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6320_, v_isExporting_boxed_6323_, v_x_6322_);
v_r_6325_ = lean_box(v_res_6324_);
return v_r_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6326_, lean_object* v_toPure_6327_, lean_object* v_className_6328_, lean_object* v_env_6329_){
_start:
{
lean_object* v___y_6331_; lean_object* v___x_6339_; lean_object* v_toEnvExtension_6340_; lean_object* v_asyncMode_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v_defaultInstances_6344_; lean_object* v___x_6345_; 
v___x_6339_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6340_ = lean_ctor_get(v___x_6339_, 0);
v_asyncMode_6341_ = lean_ctor_get(v_toEnvExtension_6340_, 2);
v___x_6342_ = lean_box(0);
lean_inc_ref(v_env_6329_);
v___x_6343_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6326_, v___x_6339_, v_env_6329_, v_asyncMode_6341_, v___x_6342_);
v_defaultInstances_6344_ = lean_ctor_get(v___x_6343_, 0);
lean_inc(v_defaultInstances_6344_);
lean_dec(v___x_6343_);
v___x_6345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6344_, v_className_6328_);
lean_dec(v_defaultInstances_6344_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_object* v___x_6346_; 
v___x_6346_ = lean_box(0);
v___y_6331_ = v___x_6346_;
goto v___jp_6330_;
}
else
{
lean_object* v_val_6347_; 
v_val_6347_ = lean_ctor_get(v___x_6345_, 0);
lean_inc(v_val_6347_);
lean_dec_ref_known(v___x_6345_, 1);
v___y_6331_ = v_val_6347_;
goto v___jp_6330_;
}
v___jp_6330_:
{
uint8_t v_isExporting_6332_; 
v_isExporting_6332_ = lean_ctor_get_uint8(v_env_6329_, sizeof(void*)*13);
if (v_isExporting_6332_ == 0)
{
lean_object* v___x_6333_; 
lean_dec_ref(v_env_6329_);
v___x_6333_ = lean_apply_2(v_toPure_6327_, lean_box(0), v___y_6331_);
return v___x_6333_;
}
else
{
lean_object* v___x_6334_; lean_object* v___f_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; 
v___x_6334_ = lean_box(v_isExporting_6332_);
v___f_6335_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6335_, 0, v_env_6329_);
lean_closure_set(v___f_6335_, 1, v___x_6334_);
v___x_6336_ = lean_box(0);
v___x_6337_ = l_List_filterTR_loop___redArg(v___f_6335_, v___y_6331_, v___x_6336_);
v___x_6338_ = lean_apply_2(v_toPure_6327_, lean_box(0), v___x_6337_);
return v___x_6338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6348_, lean_object* v_toPure_6349_, lean_object* v_className_6350_, lean_object* v_env_6351_){
_start:
{
lean_object* v_res_6352_; 
v_res_6352_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6348_, v_toPure_6349_, v_className_6350_, v_env_6351_);
lean_dec(v_className_6350_);
return v_res_6352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6353_, lean_object* v_inst_6354_, lean_object* v_className_6355_){
_start:
{
lean_object* v_toApplicative_6356_; lean_object* v_toBind_6357_; lean_object* v_getEnv_6358_; lean_object* v_toPure_6359_; lean_object* v___x_6360_; lean_object* v___f_6361_; lean_object* v___x_6362_; 
v_toApplicative_6356_ = lean_ctor_get(v_inst_6353_, 0);
lean_inc_ref(v_toApplicative_6356_);
v_toBind_6357_ = lean_ctor_get(v_inst_6353_, 1);
lean_inc(v_toBind_6357_);
lean_dec_ref(v_inst_6353_);
v_getEnv_6358_ = lean_ctor_get(v_inst_6354_, 0);
lean_inc(v_getEnv_6358_);
lean_dec_ref(v_inst_6354_);
v_toPure_6359_ = lean_ctor_get(v_toApplicative_6356_, 1);
lean_inc(v_toPure_6359_);
lean_dec_ref(v_toApplicative_6356_);
v___x_6360_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6361_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6361_, 0, v___x_6360_);
lean_closure_set(v___f_6361_, 1, v_toPure_6359_);
lean_closure_set(v___f_6361_, 2, v_className_6355_);
v___x_6362_ = lean_apply_4(v_toBind_6357_, lean_box(0), lean_box(0), v_getEnv_6358_, v___f_6361_);
return v___x_6362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6363_, lean_object* v_inst_6364_, lean_object* v_inst_6365_, lean_object* v_className_6366_){
_start:
{
lean_object* v___x_6367_; 
v___x_6367_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6364_, v_inst_6365_, v_className_6366_);
return v___x_6367_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPBinder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_UnusedBinders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPBinder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_UnusedBinders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_synthInstance_checkSynthOrder = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_synthInstance_checkSynthOrder);
lean_dec_ref(res);
l_Lean_Meta_instInhabitedInstanceEntry_default = _init_l_Lean_Meta_instInhabitedInstanceEntry_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedInstanceEntry_default);
l_Lean_Meta_instInhabitedInstanceEntry = _init_l_Lean_Meta_instInhabitedInstanceEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedInstanceEntry);
l_Lean_Meta_instInhabitedInstances_default = _init_l_Lean_Meta_instInhabitedInstances_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedInstances_default);
l_Lean_Meta_instInhabitedInstances = _init_l_Lean_Meta_instInhabitedInstances();
lean_mark_persistent(l_Lean_Meta_instInhabitedInstances);
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_instanceExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_instanceExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_defaultInstanceExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_defaultInstanceExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPBinder(uint8_t builtin);
lean_object* initialize_Lean_Util_UnusedBinders(uint8_t builtin);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPBinder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_UnusedBinders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OriginalConstKind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
